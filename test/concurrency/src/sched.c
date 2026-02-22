/**
 * @file sched.c
 * @brief Controlled thread scheduling implementation.
 */

#include "../include/sched.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <time.h>

/* Global scheduler state */
sched_state_t g_sched = {0};

/* Thread-local thread ID (1-indexed, 0 = not a scheduled thread) */
__thread int tl_sched_thread_id = 0;

/* Thread wrapper data */
typedef struct {
    int thread_id;
    sched_thread_fn fn;
    void *data;
} thread_wrapper_data_t;

/* Get current time in milliseconds */
static int64_t get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Check if a point is in the sync point set */
static bool is_sync_point(const char *point) {
    for (int i = 0; i < g_sched.num_sync_points; i++) {
        if (strcmp(g_sched.sync_points[i], point) == 0) {
            return true;
        }
    }
    return false;
}

/* Add a point to the sync point set (if not already present) */
static void add_sync_point(const char *point) {
    if (is_sync_point(point)) return;
    if (g_sched.num_sync_points >= SCHED_MAX_SYNC_POINTS) return;
    strncpy(g_sched.sync_points[g_sched.num_sync_points], point, SCHED_MAX_POINT_LEN - 1);
    g_sched.sync_points[g_sched.num_sync_points][SCHED_MAX_POINT_LEN - 1] = '\0';
    g_sched.num_sync_points++;
}

/* Thread wrapper function */
static void *thread_wrapper(void *arg) {
    thread_wrapper_data_t *wrap = (thread_wrapper_data_t *)arg;
    int tid = wrap->thread_id;
    sched_thread_fn fn = wrap->fn;
    void *data = wrap->data;
    free(wrap);
    
    /* Set thread-local ID */
    tl_sched_thread_id = tid;
    
    /* Run the user's thread function */
    fn(tid, data);
    
    /* Mark thread as done */
    pthread_mutex_lock(&g_sched.mutex);
    g_sched.thread_done[tid] = true;
    strncpy(g_sched.thread_point[tid], "__done__", SCHED_MAX_POINT_LEN - 1);
    pthread_cond_signal(&g_sched.sched_cond);
    pthread_mutex_unlock(&g_sched.mutex);
    
    return NULL;
}

void sched_init(void) {
    memset(&g_sched, 0, sizeof(g_sched));
    pthread_mutex_init(&g_sched.mutex, NULL);
    pthread_cond_init(&g_sched.sched_cond, NULL);
    for (int i = 0; i < SCHED_MAX_THREADS; i++) {
        pthread_cond_init(&g_sched.thread_cond[i], NULL);
    }
    g_sched.enabled = false;
}

void sched_fini(void) {
    pthread_mutex_destroy(&g_sched.mutex);
    pthread_cond_destroy(&g_sched.sched_cond);
    for (int i = 0; i < SCHED_MAX_THREADS; i++) {
        pthread_cond_destroy(&g_sched.thread_cond[i]);
    }
    memset(&g_sched, 0, sizeof(g_sched));
}

int sched_run(sched_config_t *config) {
    if (config->num_threads > SCHED_MAX_THREADS) {
        fprintf(stderr, "sched_run: too many threads (%d > %d)\n", 
            config->num_threads, SCHED_MAX_THREADS);
        return -1;
    }
    
    int timeout_ms = config->timeout_ms > 0 ? config->timeout_ms : 5000;
    
    /* Initialize state */
    pthread_mutex_lock(&g_sched.mutex);
    g_sched.num_threads = config->num_threads;
    g_sched.enabled = true;
    g_sched.failed = false;
    g_sched.fail_reason[0] = '\0';
    g_sched.num_sync_points = 0;
    
    /* Build the sync point set from the schedule.
     * Threads will only block at points in this set. */
    for (int i = 0; i < config->schedule_len; i++) {
        if (config->schedule[i].thread_id == 0) break;
        add_sync_point(config->schedule[i].point);
    }
    
    for (int i = 1; i <= config->num_threads; i++) {
        g_sched.thread_point[i][0] = '\0';
        g_sched.thread_proceed[i] = false;
        g_sched.thread_done[i] = false;
    }
    pthread_mutex_unlock(&g_sched.mutex);
    
    /* Spawn worker threads */
    pthread_t threads[SCHED_MAX_THREADS];
    for (int i = 1; i <= config->num_threads; i++) {
        thread_wrapper_data_t *wrap = malloc(sizeof(thread_wrapper_data_t));
        wrap->thread_id = i;
        /* Use per-thread function if provided, otherwise fall back to common function */
        wrap->fn = config->thread_fns[i] ? config->thread_fns[i] : config->thread_fn;
        wrap->data = config->thread_data;
        
        if (wrap->fn == NULL) {
            fprintf(stderr, "sched_run: no function for thread %d\n", i);
            free(wrap);
            g_sched.enabled = false;
            return -1;
        }
        
        if (pthread_create(&threads[i], NULL, thread_wrapper, wrap) != 0) {
            fprintf(stderr, "sched_run: pthread_create failed for thread %d\n", i);
            g_sched.enabled = false;
            return -1;
        }
    }
    
    /* Execute the schedule */
    int result = 0;
    for (int step = 0; step < config->schedule_len; step++) {
        sched_step_t *s = &config->schedule[step];
        if (s->thread_id == 0) break; /* End marker */
        
        int tid = s->thread_id;
        const char *point = s->point;
        
        pthread_mutex_lock(&g_sched.mutex);
        
        /* Wait for thread to reach the barrier point (with timeout) */
        int64_t deadline = get_time_ms() + timeout_ms;
        while (strcmp(g_sched.thread_point[tid], point) != 0 && 
               !g_sched.thread_done[tid]) {
            
            struct timespec ts;
            ts.tv_sec = deadline / 1000;
            ts.tv_nsec = (deadline % 1000) * 1000000;
            
            int rc = pthread_cond_timedwait(&g_sched.sched_cond, &g_sched.mutex, &ts);
            if (rc == ETIMEDOUT) {
                snprintf(g_sched.fail_reason, sizeof(g_sched.fail_reason),
                    "Timeout at step %d: waiting for thread %d at point '%s' "
                    "(thread is at '%s')",
                    step, tid, point, g_sched.thread_point[tid]);
                g_sched.failed = true;
                result = -1;
                break;
            }
        }
        
        if (g_sched.failed) {
            pthread_mutex_unlock(&g_sched.mutex);
            break;
        }
        
        if (g_sched.thread_done[tid]) {
            snprintf(g_sched.fail_reason, sizeof(g_sched.fail_reason),
                "Thread %d finished before reaching point '%s' at step %d",
                tid, point, step);
            g_sched.failed = true;
            result = -1;
            pthread_mutex_unlock(&g_sched.mutex);
            break;
        }
        
        /* Release the thread */
        g_sched.thread_proceed[tid] = true;
        pthread_cond_signal(&g_sched.thread_cond[tid]);
        
        /* Wait for the thread to move past this point (reach next point or finish) */
        /* This ensures the action after SCHED_POINT completes before we proceed */
        int64_t proceed_deadline = get_time_ms() + timeout_ms;
        while (strcmp(g_sched.thread_point[tid], point) == 0 && 
               !g_sched.thread_done[tid] && g_sched.enabled) {
            struct timespec ts;
            ts.tv_sec = proceed_deadline / 1000;
            ts.tv_nsec = (proceed_deadline % 1000) * 1000000;
            int rc = pthread_cond_timedwait(&g_sched.sched_cond, &g_sched.mutex, &ts);
            if (rc == ETIMEDOUT) {
                snprintf(g_sched.fail_reason, sizeof(g_sched.fail_reason),
                    "Timeout at step %d: thread %d stuck at point '%s'",
                    step, tid, point);
                g_sched.failed = true;
                result = -1;
                break;
            }
        }
        
        pthread_mutex_unlock(&g_sched.mutex);
        
        if (g_sched.failed) {
            break;
        }
    }
    
    /* Let all remaining threads finish */
    pthread_mutex_lock(&g_sched.mutex);
    for (int i = 1; i <= config->num_threads; i++) {
        g_sched.thread_proceed[i] = true;
        pthread_cond_signal(&g_sched.thread_cond[i]);
    }
    g_sched.enabled = false;
    pthread_mutex_unlock(&g_sched.mutex);
    
    /* Join all threads */
    for (int i = 1; i <= config->num_threads; i++) {
        pthread_join(threads[i], NULL);
    }
    
    if (result != 0) {
        fprintf(stderr, "sched_run FAILED: %s\n", g_sched.fail_reason);
    }
    
    return result;
}

void sched_point(const char *point) {
    int tid = tl_sched_thread_id;
    if (tid == 0 || !g_sched.enabled) {
        return; /* Not a scheduled thread or scheduling disabled */
    }
    
    /* AUTO-RELEASE: If this point is not in the schedule, pass through */
    if (!is_sync_point(point)) {
        return;
    }
    
    pthread_mutex_lock(&g_sched.mutex);
    
    /* Record that we've arrived at this point */
    strncpy(g_sched.thread_point[tid], point, SCHED_MAX_POINT_LEN - 1);
    g_sched.thread_point[tid][SCHED_MAX_POINT_LEN - 1] = '\0';
    
    /* Signal scheduler that we've arrived */
    pthread_cond_signal(&g_sched.sched_cond);
    
    /* Wait for permission to proceed */
    while (!g_sched.thread_proceed[tid] && g_sched.enabled) {
        pthread_cond_wait(&g_sched.thread_cond[tid], &g_sched.mutex);
    }
    g_sched.thread_proceed[tid] = false;
    
    /* DON'T clear the point here - the scheduler will wait for us to move */
    /* The point will be overwritten when we reach the next SCHED_POINT */
    
    pthread_mutex_unlock(&g_sched.mutex);
}

/* Exported function for Flecs to call (matches declaration in os_api.h) */
__attribute__((visibility("default")))
void flecs_sched_point(const char *point) {
    sched_point(point);
}
