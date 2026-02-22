/**
 * @file EnsureDirectWriteRace.c
 * @brief Test suite for ecs_ensure direct-write race.
 *
 * Bug: When ecs_ensure is called from multiple threads on the same entity
 * that already has the component, flecs_defer_get_existing returns a raw
 * pointer to the live component data. Unlike flecs_defer_set which has a
 * stage_count guard, ecs_ensure does NOT guard against multi-stage scenarios.
 * Both workers receive the SAME raw pointer and write to it concurrently.
 *
 * TLA+ spec: EnsureDirectWrite.tla
 * Location: src/commands.c:399-459 (flecs_defer_ensure)
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
    
    /* Use per-thread stage */
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Begin deferring - this is required for the deferred ensure path */
    ecs_defer_begin(stage);
    
    /* Get mutable pointer to component - this is the race-prone operation.
     * For entities that already have the component, this returns a raw pointer
     * to the live data without any protection in multi-stage mode. */
    Position *p = ecs_ensure_id(stage, td->entity, td->component_id, sizeof(Position));
    
    /* Modify the component - concurrent modifications are the bug */
    p->x += (float)thread_id;
    p->y += (float)thread_id;
    
    /* End deferring */
    ecs_defer_end(stage);
}

/**
 * Test: concurrent_raw_ptrs
 *
 * Forces both threads to obtain raw pointers before either writes,
 * demonstrating the race window where both hold pointers to live data.
 */
void EnsureDirectWriteRace_concurrent_raw_ptrs(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    /* Entity must already have the component for the bug to manifest.
     * If entity doesn't have it, ecs_ensure allocates in stage storage. */
    ecs_entity_t e = ecs_new(world);
    ecs_set(world, e, Position, {0, 0});
    
    EnsureTestData td = {
        .world = world,
        .entity = e,
        .component_id = ecs_id(Position)
    };
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
            /* Both threads get raw pointers, then both have them simultaneously */
            SCHED_STEP(1, "ensure_get_ptr"),
            SCHED_STEP(2, "ensure_get_ptr"),
            SCHED_STEP(1, "ensure_has_ptr"),
            SCHED_STEP(2, "ensure_has_ptr"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_fini(world);
}

/**
 * Test: sequential_writes
 *
 * Shows that sequential access (T1 gets ptr and finishes, then T2)
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
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Sequential: T1 completes before T2 starts */
            SCHED_STEP(1, "ensure_get_ptr"),
            SCHED_STEP(1, "ensure_has_ptr"),
            SCHED_STEP(2, "ensure_get_ptr"),
            SCHED_STEP(2, "ensure_has_ptr"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    test_assert(result == 0);
    
    ecs_fini(world);
}
