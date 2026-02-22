/**
 * @file OrderBySortRace.c
 * @brief Test suite for Bug 6: order_by sorting race.
 *
 * Bug: When multiple threads trigger re-sorting of query results via
 * order_by, concurrent access to the sorting data structures can cause
 * corruption or lost match counts.
 *
 * TODO: Instrument order_by.c:228-316 with FLECS_SCHED_POINT macros
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_query_t *queries[3];  /* Per-thread queries (index 1 and 2 used) */
} OrderByTestData;

/* Comparison function for order_by */
static int compare_position(ecs_entity_t e1, const void *p1,
                            ecs_entity_t e2, const void *p2)
{
    (void)e1; (void)e2;
    const Position *pos1 = p1;
    const Position *pos2 = p2;
    return (pos1->x > pos2->x) - (pos1->x < pos2->x);
}

/* Thread function that iterates a sorted query */
static void worker_fn(int thread_id, void *data) {
    OrderByTestData *td = (OrderByTestData *)data;
    
    /* Use per-thread stage and query */
    ecs_world_t *stage = td->stages[thread_id];
    ecs_query_t *q = td->queries[thread_id];
    
    /* Iterate the sorted query - this can trigger re-sorting */
    ecs_iter_t it = ecs_query_iter(stage, q);
    while (ecs_query_next(&it)) {
        Position *p = ecs_field(&it, Position, 0);
        (void)p;
    }
}

/**
 * Test: concurrent_sort
 *
 * Forces both threads to trigger sorting simultaneously.
 *
 * NOTE: This test is a placeholder. Full functionality requires
 * instrumenting order_by.c.
 */
void OrderBySortRace_concurrent_sort(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    /* Create entities with varying positions */
    for (int i = 0; i < 100; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)(100 - i), (float)i});
    }
    
    OrderByTestData td = { .world = world };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Create per-thread queries in the main thread (thread-safe) */
    td.queries[1] = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position,
        .cache_kind = EcsQueryCacheAuto
    });
    td.queries[2] = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position,
        .cache_kind = EcsQueryCacheAuto
    });
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 0,  /* No schedule yet */
        .schedule = {
            /* TODO: Add schedule once order_by.c is instrumented */
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_query_fini(td.queries[1]);
    ecs_query_fini(td.queries[2]);
    ecs_fini(world);
}

/**
 * Test: lost_match_count
 *
 * Forces interleaving that causes match count to be incorrect.
 */
void OrderBySortRace_lost_match_count(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 100; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)(100 - i), (float)i});
    }
    
    OrderByTestData td = { .world = world };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Create per-thread queries in the main thread (thread-safe) */
    td.queries[1] = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position,
        .cache_kind = EcsQueryCacheAuto
    });
    td.queries[2] = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position,
        .cache_kind = EcsQueryCacheAuto
    });
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 0,
        .schedule = { SCHED_END }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_query_fini(td.queries[1]);
    ecs_query_fini(td.queries[2]);
    ecs_fini(world);
}
