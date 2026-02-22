/**
 * @file sched.h
 * @brief Controlled thread scheduling for deterministic race reproduction.
 *
 * This framework allows tests to force specific thread interleavings that
 * trigger race conditions. It works by inserting barrier points in the code
 * under test, and having a scheduler that controls which thread proceeds
 * through each barrier and in what order.
 *
 * Usage:
 *   1. Instrument code with SCHED_POINT("name") at race-prone locations
 *   2. Define a schedule (sequence of thread/point pairs)
 *   3. Call sched_run() to execute threads with controlled interleaving
 */

#ifndef FLECS_SCHED_H
#define FLECS_SCHED_H

#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Maximum number of threads the scheduler can handle */
#define SCHED_MAX_THREADS 16

/* Maximum length of a schedule */
#define SCHED_MAX_STEPS 256

/* Maximum length of a point name */
#define SCHED_MAX_POINT_LEN 64

/* Maximum number of sync points (points where threads block) */
#define SCHED_MAX_SYNC_POINTS 64

/**
 * A step in the schedule: release thread `thread_id` when it reaches `point`.
 */
typedef struct sched_step_t {
    int thread_id;                    /* Thread to release (1-indexed, 0 = end) */
    char point[SCHED_MAX_POINT_LEN];  /* Barrier point name */
} sched_step_t;

/**
 * Thread function type. Receives thread_id (1-indexed) and user data.
 */
typedef void (*sched_thread_fn)(int thread_id, void *data);

/**
 * Configuration for a scheduled test run.
 */
typedef struct sched_config_t {
    int num_threads;                      /* Number of worker threads */
    sched_thread_fn thread_fn;            /* Function each thread executes (fallback) */
    sched_thread_fn thread_fns[SCHED_MAX_THREADS]; /* Per-thread functions (optional) */
    void *thread_data;                    /* User data passed to thread_fn */
    sched_step_t schedule[SCHED_MAX_STEPS]; /* The interleaving schedule */
    int schedule_len;                     /* Number of steps in schedule */
    int timeout_ms;                       /* Timeout per step (default 5000) */
} sched_config_t;

/**
 * Global scheduler state (thread-local access via sched_get_thread_id).
 */
typedef struct sched_state_t {
    pthread_mutex_t mutex;
    pthread_cond_t sched_cond;            /* Scheduler waits on this */
    pthread_cond_t thread_cond[SCHED_MAX_THREADS]; /* Threads wait on these */
    
    char thread_point[SCHED_MAX_THREADS][SCHED_MAX_POINT_LEN]; /* Current point */
    bool thread_proceed[SCHED_MAX_THREADS]; /* Permission to proceed */
    bool thread_done[SCHED_MAX_THREADS];    /* Thread finished */
    int num_threads;
    
    /* Sync points: threads only block at points in this set */
    char sync_points[SCHED_MAX_SYNC_POINTS][SCHED_MAX_POINT_LEN];
    int num_sync_points;
    
    bool enabled;                         /* Is scheduling active? */
    bool failed;                          /* Did scheduling fail (timeout)? */
    char fail_reason[256];
} sched_state_t;

/* Global scheduler state */
extern sched_state_t g_sched;

/* Thread-local thread ID */
extern __thread int tl_sched_thread_id;

/**
 * Initialize the scheduler. Call before sched_run().
 */
void sched_init(void);

/**
 * Cleanup the scheduler. Call after sched_run().
 */
void sched_fini(void);

/**
 * Run a test with controlled scheduling.
 * 
 * @param config Configuration specifying threads, schedule, etc.
 * @return 0 on success, -1 on failure (timeout, etc.)
 */
int sched_run(sched_config_t *config);

/**
 * Barrier point. Called from instrumented code.
 * Blocks until the scheduler releases this thread at this point.
 *
 * @param point Name of this barrier point.
 */
void sched_point(const char *point);

/**
 * Get the current thread's ID (1-indexed).
 * Returns 0 if not in a scheduled thread.
 */
static inline int sched_get_thread_id(void) {
    return tl_sched_thread_id;
}

/**
 * Check if scheduling is currently active.
 */
static inline bool sched_is_active(void) {
    return g_sched.enabled;
}

/**
 * Macro for instrumentation. Use this in code under test.
 * No-op when scheduling is not active (production builds).
 */
#ifdef FLECS_SCHED_TESTING
    #define SCHED_POINT(name) do { \
        if (sched_is_active()) { \
            sched_point(name); \
        } \
    } while(0)
#else
    #define SCHED_POINT(name) ((void)0)
#endif

/**
 * Helper macro to define a schedule inline.
 */
#define SCHED_STEP(tid, pt) { .thread_id = (tid), .point = pt }
#define SCHED_END { .thread_id = 0, .point = "" }

#ifdef __cplusplus
}
#endif

#endif /* FLECS_SCHED_H */
