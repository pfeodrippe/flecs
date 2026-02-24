/**
 * @file DirtyStateRace.c
 * @brief Test suite for dirty_state ++ lost increment race.
 *
 * When multiple workers concurrently mark fields as dirty, the
 * non-atomic read-modify-write on dirty_state[column+1]++ can lose
 * increments, causing change detection to miss modifications.
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_query_t *query;
} DirtyStateTestData;

/* Thread function that iterates a query and modifies fields. */
static void worker_fn(int thread_id, void *data) {
    DirtyStateTestData *td = (DirtyStateTestData *)data;
    
    /* Use per-thread stage to avoid stack allocator conflicts */
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Iterate the query - triggers dirty marking on writes */
    ecs_iter_t it = ecs_query_iter(stage, td->query);
    while (ecs_query_next(&it)) {
        Position *p = ecs_field(&it, Position, 0);
        for (int i = 0; i < it.count; i++) {
            p[i].x += 1.0f;
        }
    }
}

/**
 * Test: lost_increment
 *
 * Forces the interleaving where both threads read the dirty counter
 * before either writes, causing one increment to be lost.
 */
void DirtyStateRace_lost_increment(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    /* Keep one table with one row to make dirty-state effects deterministic. */
    ecs_set(world, ecs_new(world), Position, {0.0f, 0.0f});
    
    /* Create a cached query with change detection AND write fields.
     * Using [out] ensures write_fields is set, which triggers dirty marking. */
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    test_assert(q != NULL);
    
    /* Initialize dirty_state by forcing change detection setup */
    ecs_iter_t init_it = ecs_query_iter(world, q);
    while (ecs_query_next(&init_it)) {}
    
    /* Force dirty state allocation by calling ecs_query_changed */
    ecs_query_changed(q);
    
    DirtyStateTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Interleaving that triggers lost increment:
             * T1 reads, T2 reads, T1 writes, T2 writes (overwrites T1) */
            SCHED_STEP(1, "dirty_state_read"),
            SCHED_STEP(2, "dirty_state_read"),
            SCHED_STEP(1, "dirty_state_write"),
            SCHED_STEP(2, "dirty_state_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    sched_fini();
    
    /* The test passes if we could reproduce the interleaving. */
    test_assert(result == 0);
    /* Bug final state: expected 2 (not 3) because one dirty_state increment is lost. */
    test_int(flecs_query_cache_get_dirty_state(q, 1), 2);
    
    ecs_query_fini(q);
    ecs_fini(world);
}

/**
 * Test: correct_interleaving
 *
 * Shows that sequential execution (T1 reads, T1 writes, T2 reads, T2 writes)
 * correctly counts all dirty state increments.
 */
void DirtyStateRace_correct_interleaving(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    ecs_set(world, ecs_new(world), Position, {0.0f, 0.0f});
    
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    test_assert(q != NULL);
    
    /* Initialize dirty_state by forcing change detection setup */
    ecs_iter_t init_it = ecs_query_iter(world, q);
    while (ecs_query_next(&init_it)) {}
    
    /* Force dirty state allocation by calling ecs_query_changed */
    ecs_query_changed(q);
    
    DirtyStateTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Correct interleaving: T1 completes before T2 starts */
            SCHED_STEP(1, "dirty_state_read"),
            SCHED_STEP(1, "dirty_state_write"),
            SCHED_STEP(2, "dirty_state_read"),
            SCHED_STEP(2, "dirty_state_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();

    test_assert(result == 0);
    /* Control final state: expected 3 because both increments are applied sequentially. */
    test_int(flecs_query_cache_get_dirty_state(q, 1), 3);
    
    ecs_query_fini(q);
    ecs_fini(world);
}
