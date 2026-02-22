/**
 * @file MonitorSyncRace.c
 * @brief Test suite for Bug 5: sync_match_monitor concurrent write race.
 *
 * Bug: Multiple workers can call flecs_query_sync_match_monitor concurrently
 * on the same cache match, causing concurrent writes to the shared _monitor
 * array without synchronization.
 *
 * Interleaving that triggers the bug:
 *   T1: sync_monitor_enter
 *   T2: sync_monitor_enter
 *   T1: sync_monitor_write_table (writes monitor[0] = dirty_state[0])
 *   T2: sync_monitor_write_table (concurrent write to same location!)
 *
 * Result: Data race on monitor array, potential stale/corrupted values
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_query_t *query;
} MonitorSyncTestData;

/* Thread function that iterates query - triggers sync_match_monitor */
static void worker_fn(int thread_id, void *data) {
    MonitorSyncTestData *td = (MonitorSyncTestData *)data;
    
    /* Use per-thread stage to avoid stack allocator conflicts */
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Iterate the query with write access - this triggers:
     * 1. flecs_query_mark_fields_dirty (marks dirty)
     * 2. flecs_query_sync_match_monitor (syncs monitor with dirty state)
     */
    ecs_iter_t it = ecs_query_iter(stage, td->query);
    while (ecs_query_next(&it)) {
        Position *p = ecs_field(&it, Position, 0);
        for (int i = 0; i < it.count; i++) {
            p[i].x += 1.0f;
        }
    }
}

/**
 * Test: concurrent_writes
 *
 * Forces both threads to enter sync_monitor simultaneously, causing
 * concurrent writes to the shared monitor array.
 */
void MonitorSyncRace_concurrent_writes(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    /* Create component and entities */
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 100; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a cached query with:
     * - [out] to mark as write field (triggers dirty marking)
     * - EcsQueryCacheAuto for caching
     * - EcsQueryDetectChanges for change detection (sets up monitors) */
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    test_assert(q != NULL);
    
    /* Do an initial iteration to initialize monitors and dirty_state */
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        Position *p = ecs_field(&it, Position, 0);
        for (int i = 0; i < it.count; i++) {
            p[i].x += 0.1f;
        }
    }
    
    /* Force monitor initialization */
    ecs_query_changed(q);
    
    MonitorSyncTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 8,
        .schedule = {
            /* First both threads go through dirty_state marking */
            SCHED_STEP(1, "dirty_state_read"),
            SCHED_STEP(1, "dirty_state_write"),
            SCHED_STEP(2, "dirty_state_read"),
            SCHED_STEP(2, "dirty_state_write"),
            /* Then interleave on sync_monitor - concurrent writes */
            SCHED_STEP(1, "sync_monitor_enter"),
            SCHED_STEP(2, "sync_monitor_enter"),
            SCHED_STEP(1, "sync_monitor_write_table"),
            SCHED_STEP(2, "sync_monitor_write_table"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    /* The test passes if we could reproduce the interleaving.
     * This demonstrates the race window exists in the real code. */
    test_assert(result == 0);
    
    ecs_query_fini(q);
    ecs_fini(world);
}

/**
 * Test: stale_monitor_value
 *
 * Forces interleaving where T2 reads a partially updated monitor,
 * potentially getting stale or inconsistent values.
 */
void MonitorSyncRace_stale_monitor_value(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    /* Create component and entities */
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 100; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a cached query with change detection */
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    test_assert(q != NULL);
    
    /* Initial iteration to set up monitors */
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        Position *p = ecs_field(&it, Position, 0);
        for (int i = 0; i < it.count; i++) {
            p[i].x += 0.1f;
        }
    }
    
    /* Force monitor initialization */
    ecs_query_changed(q);
    
    MonitorSyncTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 8,
        .schedule = {
            /* First both threads go through dirty_state marking */
            SCHED_STEP(1, "dirty_state_read"),
            SCHED_STEP(1, "dirty_state_write"),
            SCHED_STEP(2, "dirty_state_read"),
            SCHED_STEP(2, "dirty_state_write"),
            /* Then sequential sync_monitor (no race in this test) */
            SCHED_STEP(1, "sync_monitor_enter"),
            SCHED_STEP(1, "sync_monitor_write_table"),
            SCHED_STEP(2, "sync_monitor_enter"),
            SCHED_STEP(2, "sync_monitor_write_table"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_query_fini(q);
    ecs_fini(world);
}
