/**
 * @file TimeSpentRace.c
 * @brief Test suite for Bug 2: time_spent += lost update race.
 *
 * Bug: When EcsWorldMeasureSystemTime is enabled and multiple threads run
 * the same system concurrently, the non-atomic read-modify-write on 
 * system_data->time_spent can lose time measurements.
 *
 * Interleaving that triggers the bug:
 *   T1: time_spent_read  (reads old_time = 0)
 *   T2: time_spent_read  (reads old_time = 0)
 *   T1: time_spent_write (writes old_time + delta1 = delta1)
 *   T2: time_spent_write (writes old_time + delta2 = delta2, overwrites T1's delta!)
 *
 * Result: Final time_spent = delta2 instead of delta1 + delta2 (lost update)
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];  /* Per-thread stages (index 1 and 2 used) */
    ecs_entity_t system;
} TimeSpentTestData;

/* Minimal system callback - just needs to run */
static void DummySystem(ecs_iter_t *it) {
    (void)it;
    /* Ensure non-trivial measurable work per worker invocation. */
    volatile int sink = 0;
    for (int i = 0; i < 200000; i++) {
        sink += i;
    }
    (void)sink;
}

/* Thread function that runs the system as a worker */
static void worker_fn(int thread_id, void *data) {
    TimeSpentTestData *td = (TimeSpentTestData *)data;
    
    /* Each worker uses its own stage to avoid stack allocator conflicts */
    ecs_world_t *stage = td->stages[thread_id];
    ecs_run_worker(stage, td->system, thread_id - 1, 2, 1.0f, NULL);
}

/**
 * Test: lost_time_measurement
 *
 * Forces the interleaving where both threads read before either writes,
 * causing one thread's time measurement to be lost.
 */
void TimeSpentRace_lost_time_measurement(void) {
    /* Create world with time measurement enabled */
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    /* Enable system time measurement - this triggers the race */
    ecs_measure_system_time(world, true);
    
    /* Create a component and entities for the system to iterate */
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 10; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a multi-threaded system */
    ecs_entity_t sys = ecs_system(world, {
        .entity = ecs_entity(world, {.name = "MeasuredSystem"}),
        .query.terms = {{.id = ecs_id(Position)}},
        .callback = DummySystem,
        .multi_threaded = true
    });
    
    TimeSpentTestData td = { .world = world, .system = sys };
    /* Get per-thread stages */
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Interleaving that triggers lost update:
             * T1 reads, T2 reads, T1 writes, T2 writes (overwrites T1) */
            SCHED_STEP(1, "time_spent_read"),
            SCHED_STEP(2, "time_spent_read"),
            SCHED_STEP(1, "time_spent_write"),
            SCHED_STEP(2, "time_spent_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    /* Lost-update run should produce a smaller final aggregate than
     * a sequential run over the same workload. */
    test_assert(result == 0);
    float raced_spent = flecs_system_get_time_spent(world, sys);
    /* Raced run must still record non-zero work before comparison. */
    test_assert(raced_spent > 0.0f);

    sched_fini();

    ecs_system_t *sys_data = (ecs_system_t*)ecs_system_get(world, sys);
    test_assert(sys_data != NULL);
    sys_data->time_spent = 0;

    sched_init();
    sched_config_t seq_config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            SCHED_STEP(1, "time_spent_read"),
            SCHED_STEP(1, "time_spent_write"),
            SCHED_STEP(2, "time_spent_read"),
            SCHED_STEP(2, "time_spent_write"),
            SCHED_END
        }
    };

    int seq_result = sched_run(&seq_config);
    test_assert(seq_result == 0);
    float seq_spent = flecs_system_get_time_spent(world, sys);
    /* Bug final state: raced aggregate is lower because one time update is lost. */
    test_assert(seq_spent > raced_spent);

    sched_fini();
    
    ecs_fini(world);
}

/**
 * Test: correct_interleaving
 *
 * Shows that sequential execution (T1 reads, T1 writes, T2 reads, T2 writes)
 * does not lose time measurements.
 */
void TimeSpentRace_correct_interleaving(void) {
    /* Create world with time measurement enabled */
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    /* Enable system time measurement */
    ecs_measure_system_time(world, true);
    
    /* Create a component and entities for the system to iterate */
    ECS_COMPONENT(world, Position);
    
    for (int i = 0; i < 10; i++) {
        ecs_entity_t e = ecs_new(world);
        ecs_set(world, e, Position, {(float)i, (float)i});
    }
    
    /* Create a multi-threaded system */
    ecs_entity_t sys = ecs_system(world, {
        .entity = ecs_entity(world, {.name = "MeasuredSystem"}),
        .query.terms = {{.id = ecs_id(Position)}},
        .callback = DummySystem,
        .multi_threaded = true
    });
    
    TimeSpentTestData td = { .world = world, .system = sys };
    /* Get per-thread stages */
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Set up the scheduler */
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 4,
        .schedule = {
            /* Correct interleaving: T1 completes before T2 starts */
            SCHED_STEP(1, "time_spent_read"),
            SCHED_STEP(1, "time_spent_write"),
            SCHED_STEP(2, "time_spent_read"),
            SCHED_STEP(2, "time_spent_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    /* With sequential execution, both measurements are correctly recorded. */
    test_assert(result == 0);
    /* Control final state: sequential path records positive accumulated time. */
    test_assert(flecs_system_get_time_spent(world, sys) > 0.0f);

    sched_fini();
    
    ecs_fini(world);
}
