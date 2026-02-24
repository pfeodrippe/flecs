/**
 * @file MonitorAllocRace.c
 * @brief Test suite for Bug 7: monitor allocation race.
 *
 * Bug: When multiple workers call flecs_query_get_match_monitor concurrently
 * for the same match that doesn't have a monitor yet, both can allocate
 * monitors, causing a memory leak (one allocation is lost).
 *
 * Interleaving that triggers the bug:
 *   T1: monitor_alloc_check (sees _monitor == NULL)
 *   T2: monitor_alloc_check (sees _monitor == NULL)
 *   T1: monitor_alloc_do (allocates monitor)
 *   T2: monitor_alloc_do (allocates another monitor, leaking T1's)
 */

#include <concurrency.h>
#include <string.h>

static int trace_count_point(const char *point) {
    int len = 0;
    const sched_trace_entry_t *trace = sched_get_trace(&len);
    int count = 0;

    for (int i = 0; i < len; i ++) {
        if (!strcmp(trace[i].point, point)) {
            count ++;
        }
    }

    return count;
}

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_query_t *query;
} MonitorAllocTestData;

/* Thread function that checks if query changed.
 * This triggers monitor allocation via flecs_query_get_match_monitor
 * when called from ecs_query_changed -> flecs_query_match_check_dirty_matches. */
static void worker_fn(int thread_id, void *data) {
    MonitorAllocTestData *td = (MonitorAllocTestData *)data;
    (void)thread_id;
    
    /* ecs_query_changed triggers monitor allocation for matches */
    ecs_query_changed(td->query);
}

/**
 * Test: double_alloc_leak
 *
 * Forces both threads to check the monitor allocation condition
 * simultaneously, causing both to allocate (memory leak).
 */
void MonitorAllocRace_double_alloc_leak(void) {
    ecs_world_t *world = ecs_init();
    
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 10; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a cached query with change detection.
     * Don't iterate before threads start - we want monitor to be unallocated
     * so both threads race to allocate it. */
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    test_assert(q != NULL);
    
    MonitorAllocTestData td = { .world = world, .query = q };
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Both threads check that monitor is NULL, then both allocate */
            SCHED_STEP(1, "monitor_alloc_check"),
            SCHED_STEP(2, "monitor_alloc_check"),
            SCHED_STEP(1, "monitor_alloc_do"),
            SCHED_STEP(2, "monitor_alloc_do"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    test_assert(result == 0);
    /* Bug final state: both threads passed the NULL-monitor check (should serialize to 1). */
    test_int(trace_count_point("monitor_alloc_check"), 2);
    /* Bug final state: two allocations occurred (expected safe path is exactly 1). */
    test_int(trace_count_point("monitor_alloc_do"), 2);
    /* Final query state: monitor storage exists after the raced allocations. */
    test_assert(flecs_query_cache_get_monitor(q, 0) >= 0);

    sched_fini();
    
    ecs_query_fini(q);
    ecs_fini(world);
}
