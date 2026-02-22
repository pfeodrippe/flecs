/**
 * @file EvalCountRace.c
 * @brief Test suite for Bug 4: eval_count inconsistent atomicity race.
 *
 * Bug: eval_count is updated with ecs_os_ainc in some places but read
 * non-atomically in others (read-modify-write via ++), causing lost increments.
 *
 * Interleaving that triggers the bug:
 *   T1: eval_count_read (reads old value)
 *   T2: eval_count_read (reads same old value)
 *   T1: eval_count_write (writes old+1)
 *   T2: eval_count_write (writes old+1, losing T1's increment)
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_query_t *query;
    ecs_table_t *table;
} EvalCountTestData;

/* Thread function that calls ecs_query_has_table.
 * This triggers the non-atomic eval_count++ path when bloom filter rejects. */
static void worker_fn(int thread_id, void *data) {
    EvalCountTestData *td = (EvalCountTestData *)data;
    (void)thread_id;
    
    /* Call ecs_query_has_table - if bloom filter rejects, triggers eval_count++ */
    ecs_iter_t it;
    ecs_query_has_table(td->query, td->table, &it);
}

/**
 * Test: lost_eval_count
 *
 * Forces interleaving where eval_count is read by both threads before
 * either writes, demonstrating the lost increment bug.
 */
void EvalCountRace_lost_eval_count(void) {
    ecs_world_t *world = ecs_init();
    
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    
    /* Create entities with Position */
    for (int i = 0; i < 10; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a single entity with Velocity to get a table that won't match */
    ecs_entity_t vel_entity = ecs_new(world);
    ecs_set(world, vel_entity, Velocity, {1.0f, 1.0f});
    ecs_table_t *vel_table = ecs_get_table(world, vel_entity);
    
    /* Create query for Position - Velocity table won't match */
    ecs_query_t *q = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}}
    });
    test_assert(q != NULL);
    
    EvalCountTestData td = { 
        .world = world, 
        .query = q,
        .table = vel_table
    };
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Both threads read eval_count before either writes */
            SCHED_STEP(1, "eval_count_read"),
            SCHED_STEP(2, "eval_count_read"),
            SCHED_STEP(1, "eval_count_write"),
            SCHED_STEP(2, "eval_count_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_query_fini(q);
    ecs_fini(world);
}

/**
 * Test: correct_interleaving
 *
 * Shows that sequential eval_count access does not lose increments.
 */
void EvalCountRace_correct_interleaving(void) {
    ecs_world_t *world = ecs_init();
    
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    
    for (int i = 0; i < 10; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    ecs_entity_t vel_entity = ecs_new(world);
    ecs_set(world, vel_entity, Velocity, {1.0f, 1.0f});
    ecs_table_t *vel_table = ecs_get_table(world, vel_entity);
    
    ecs_query_t *q = ecs_query(world, {
        .terms = {{.id = ecs_id(Position)}}
    });
    test_assert(q != NULL);
    
    EvalCountTestData td = { 
        .world = world, 
        .query = q,
        .table = vel_table
    };
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Sequential: T1 completes before T2 starts */
            SCHED_STEP(1, "eval_count_read"),
            SCHED_STEP(1, "eval_count_write"),
            SCHED_STEP(2, "eval_count_read"),
            SCHED_STEP(2, "eval_count_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_query_fini(q);
    ecs_fini(world);
}
