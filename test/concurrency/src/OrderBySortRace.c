/**
 * @file OrderBySortRace.c
 * @brief Test suite for flecs_query_cache_sort_tables concurrent execution race.
 *
 * Bug: When a cached query has an order_by callback configured, multiple workers
 * calling ecs_query_iter() concurrently can cause:
 *   - Concurrent sorting of the same table (data corruption)
 *   - Lost increments to cache->match_count (non-atomic ++)
 *   - Concurrent writes to cache->table_slices
 *
 * TLA+ spec: OrderBySortRace.tla
 * Location: src/query/cache/order_by.c:228-316
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
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_query_t *query;
} OrderBySortTestData;

/* Compare function for order_by */
static int compare_position(ecs_entity_t e1, const void *p1, 
                            ecs_entity_t e2, const void *p2)
{
    (void)e1; (void)e2;
    const Position *pos1 = p1;
    const Position *pos2 = p2;
    return (pos1->x > pos2->x) - (pos1->x < pos2->x);
}

/* Thread function that iterates the query with order_by.
 * This triggers flecs_query_cache_sort_tables. */
static void worker_fn(int thread_id, void *data) {
    OrderBySortTestData *td = (OrderBySortTestData *)data;
    
    /* Use per-thread stage to avoid stack allocator conflicts */
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Iterate the query - triggers sorting for order_by queries */
    ecs_iter_t it = ecs_query_iter(stage, td->query);
    while (ecs_query_next(&it)) {
        /* Just iterate, sorting happens in query_iter */
    }
}

/**
 * Test: concurrent_sort
 *
 * Forces concurrent execution of sorting logic by having both threads
 * enter the sort phase simultaneously.
 */
void OrderBySortRace_concurrent_sort(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    /* Create entities with positions in reverse order */
    for (int i = 10; i >= 0; i--) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a cached query with order_by */
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position
    });
    test_assert(q != NULL);
    
    /* Initialize monitors by iterating once */
    ecs_iter_t init_it = ecs_query_iter(world, q);
    while (ecs_query_next(&init_it)) {}
    
    /* Add a new entity to trigger re-sort on next iteration.
     * This makes the table dirty (new row added). */
    ecs_entity_t new_e = ecs_new(world);
    ecs_set(world, new_e, Position, {50.0f, 50.0f});

    OrderBySortTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    /* Schedule: both threads hit monitor_alloc_check twice (one per term check),
     * then both hit sort_table concurrently for the race. */
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Both threads sort the same table concurrently */
            SCHED_STEP(1, "sort_table"),
            SCHED_STEP(2, "sort_table"),
            SCHED_STEP(1, "sort_match_count_read"),
            SCHED_STEP(2, "sort_match_count_read"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    test_assert(result == 0);
    /* Bug final state: both workers entered table sort path (should serialize to 1). */
    test_int(trace_count_point("sort_table"), 2);
    /* Bug precondition state: both workers read match_count before either write. */
    test_int(trace_count_point("sort_match_count_read"), 2);

    sched_fini();
    
    ecs_query_fini(q);
    ecs_fini(world);
}

/**
 * Test: lost_match_count
 *
 * Forces the interleaving where both threads read match_count before
 * either writes, causing one increment to be lost.
 */
void OrderBySortRace_lost_match_count(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    for (int i = 10; i >= 0; i--) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position",
        .cache_kind = EcsQueryCacheAuto,
        .order_by = ecs_id(Position),
        .order_by_callback = compare_position
    });
    test_assert(q != NULL);
    
    /* Initialize monitors by iterating once */
    ecs_iter_t init_it = ecs_query_iter(world, q);
    while (ecs_query_next(&init_it)) {}
    
    /* Add a new entity to trigger re-sort on next iteration */
    ecs_entity_t new_e = ecs_new(world);
    ecs_set(world, new_e, Position, {50.0f, 50.0f});

    int32_t before_match_count = ecs_query_match_count(q);
    
    OrderBySortTestData td = { .world = world, .query = q };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    /* Classic lost-update race: T1 reads, T2 reads, T1 writes, T2 writes.
     * Both read the same value, both compute same+1, T2's write overwrites T1's. */
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            SCHED_STEP(1, "sort_match_count_read"),
            SCHED_STEP(2, "sort_match_count_read"),
            SCHED_STEP(1, "sort_match_count_write"),
            SCHED_STEP(2, "sort_match_count_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    /* Bug final state: match_count rises by 1 (not 2) because one increment is lost. */
    test_int(ecs_query_match_count(q) - before_match_count, 1);
    
    ecs_query_fini(q);
    ecs_fini(world);
}
