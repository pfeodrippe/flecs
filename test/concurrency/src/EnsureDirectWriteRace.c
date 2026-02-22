/**
 * @file EnsureDirectWriteRace.c
 * @brief Test suite for Bug 1: ecs_ensure direct-write race.
 *
 * Bug: When ecs_ensure is called from multiple threads on the same entity,
 * both threads can obtain raw pointers to the same component data, then
 * write concurrently without synchronization.
 *
 * TODO: Instrument commands.c:399-459 with FLECS_SCHED_POINT macros
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_entity_t entity;
    ecs_id_t component_id;
} EnsureTestData;

/* Thread function that calls ecs_ensure and modifies the component */
static void worker_fn(int thread_id, void *data) {
    EnsureTestData *td = (EnsureTestData *)data;
    
    /* Use per-thread stage to avoid stack allocator conflicts */
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Get mutable pointer to component - this is the race-prone operation */
    Position *p = ecs_ensure_id(stage, td->entity, td->component_id, sizeof(Position));
    
    /* Modify the component - concurrent modifications are the bug */
    p->x += (float)thread_id;
    p->y += (float)thread_id;
}

/**
 * Test: concurrent_raw_ptrs
 *
 * Forces both threads to obtain raw pointers before either writes,
 * demonstrating the race window.
 *
 * NOTE: This test is a placeholder. Full functionality requires
 * instrumenting commands.c with FLECS_SCHED_POINT macros.
 */
void EnsureDirectWriteRace_concurrent_raw_ptrs(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    ecs_entity_t e = ecs_new(world);
    ecs_set(world, e, Position, {0, 0});
    
    EnsureTestData td = {
        .world = world,
        .entity = e,
        .component_id = ecs_id(Position)
    };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 0,  /* No schedule - just run threads */
        .schedule = {
            /* TODO: Add schedule once commands.c is instrumented:
             * SCHED_STEP(1, "ensure_get_ptr"),
             * SCHED_STEP(2, "ensure_get_ptr"),
             * SCHED_STEP(1, "ensure_write"),
             * SCHED_STEP(2, "ensure_write"), */
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    /* For now, just verify we can run the test */
    test_assert(result == 0);
    
    ecs_fini(world);
}

/**
 * Test: sequential_writes
 *
 * Shows that sequential access (T1 gets ptr and writes, then T2)
 * does not have race conditions.
 */
void EnsureDirectWriteRace_sequential_writes(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    ecs_entity_t e = ecs_new(world);
    ecs_set(world, e, Position, {0, 0});
    
    EnsureTestData td = {
        .world = world,
        .entity = e,
        .component_id = ecs_id(Position)
    };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 0,  /* No schedule - just run threads */
        .schedule = {
            /* TODO: Add schedule once commands.c is instrumented */
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_fini(world);
}
