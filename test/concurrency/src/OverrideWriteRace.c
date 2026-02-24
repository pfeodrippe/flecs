/**
 * @file OverrideWriteRace.c
 * @brief Test suite for override removal write race.
 *
 * Bug: When removing an overridden component during readonly/deferred mode,
 * Flecs IMMEDIATELY writes the base component value into the entity's table
 * column — bypassing the command queue. This is a direct write to shared
 * world storage from a worker thread.
 *
 * If two systems in different stages both remove the same overridden component
 * from the same entity, or one system reads a component while another removes
 * the override, there is a data race on the component memory.
 *
 * TLA+ spec: OverrideWriteRace.tla
 * Location: src/commands.c:276-312 (flecs_defer_remove override copy)
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

static int trace_first_index(const char *point) {
    int len = 0;
    const sched_trace_entry_t *trace = sched_get_trace(&len);

    for (int i = 0; i < len; i ++) {
        if (!strcmp(trace[i].point, point)) {
            return i;
        }
    }

    return -1;
}

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];
    ecs_entity_t base;      /* Prefab/base entity */
    ecs_entity_t instance;  /* Entity with override */
    ecs_id_t component_id;
    volatile bool write_in_progress;
    volatile bool read_during_write;
} OverrideTestData;

/* Thread function that removes override (triggers immediate write) */
static void worker_remove_fn(int thread_id, void *data) {
    OverrideTestData *td = (OverrideTestData *)data;
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Begin deferring - required to enter the deferred remove path */
    ecs_defer_begin(stage);
    td->write_in_progress = true;
    
    /* Removing the override triggers immediate copy from base to instance */
    ecs_remove_id(stage, td->instance, td->component_id);
    td->write_in_progress = false;
    
    /* End deferring */
    ecs_defer_end(stage);
}

/* Thread function that reads component (races with override removal) */
static void worker_read_fn(int thread_id, void *data) {
    OverrideTestData *td = (OverrideTestData *)data;
    (void)thread_id;
    
    sched_point("override_read_begin");
    td->read_during_write = td->write_in_progress;

    /* Read the component - may see torn data if another thread is writing */
    const Position *p = ecs_get_id(td->world, td->instance, td->component_id);
    if (p) {
        /* Just read the value */
        volatile float x = p->x;
        volatile float y = p->y;
        (void)x; (void)y;
    }

    sched_point("override_read_end");
}

/**
 * Test: concurrent_override_remove
 *
 * Forces both threads to enter the override write path concurrently.
 */
void OverrideWriteRace_concurrent_override_remove(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    /* Create a prefab (base entity) */
    ecs_entity_t base = ecs_new(world);
    ecs_add_id(world, base, EcsPrefab);
    ecs_set(world, base, Position, {100.0f, 100.0f});
    
    /* Create an instance that inherits from the prefab */
    ecs_entity_t instance = ecs_new_w_pair(world, EcsIsA, base);
    /* Override the Position component */
    ecs_set(world, instance, Position, {200.0f, 200.0f});
    
    OverrideTestData td = {
        .world = world,
        .base = base,
        .instance = instance,
        .component_id = ecs_id(Position)
    };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_remove_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 6,
        .schedule = {
            /* Both threads enter the override write path concurrently */
            SCHED_STEP(1, "override_write_begin"),
            SCHED_STEP(2, "override_write_begin"),
            SCHED_STEP(1, "override_write_copy"),
            SCHED_STEP(2, "override_write_copy"),
            SCHED_STEP(1, "override_write_end"),
            SCHED_STEP(2, "override_write_end"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    test_assert(result == 0);
    /* Bug final state: both workers executed immediate override copy writes. */
    test_int(trace_count_point("override_write_copy"), 2);
    /* Final entity state: override is removed so value comes from base relation. */
    test_assert(!ecs_owns_id(world, instance, td.component_id));

    sched_fini();
    
    ecs_fini(world);
}

/**
 * Test: read_during_write
 *
 * Forces one thread to read while another is writing during override removal.
 */
void OverrideWriteRace_read_during_write(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    
    ecs_entity_t base = ecs_new(world);
    ecs_add_id(world, base, EcsPrefab);
    ecs_set(world, base, Position, {100.0f, 100.0f});
    
    ecs_entity_t instance = ecs_new_w_pair(world, EcsIsA, base);
    ecs_set(world, instance, Position, {200.0f, 200.0f});
    
    OverrideTestData td = {
        .world = world,
        .base = base,
        .instance = instance,
        .component_id = ecs_id(Position)
    };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    sched_init();
    
    /* Use different worker functions - T1 removes, T2 reads */
    sched_config_t config = {
        .num_threads = 2,
        .thread_fns = {NULL, worker_remove_fn, worker_read_fn},
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 5,
        .schedule = {
            /* T1 starts write, T2 reads while T1 is in the write window. */
            SCHED_STEP(1, "override_write_begin"),
            SCHED_STEP(2, "override_read_begin"),
            SCHED_STEP(1, "override_write_copy"),
            SCHED_STEP(2, "override_read_end"),
            SCHED_STEP(1, "override_write_end"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);

    test_assert(result == 0);
    int write_begin = trace_first_index("override_write_begin");
    int read_begin = trace_first_index("override_read_begin");
    int write_end = trace_first_index("override_write_end");
    test_assert(write_begin != -1);
    test_assert(read_begin != -1);
    test_assert(write_end != -1);
    /* Bug final state: reader observed itself inside the writer's critical window. */
    test_assert(td.read_during_write);
    /* Final entity state: override ownership is removed after writer finishes. */
    test_assert(!ecs_owns_id(world, instance, td.component_id));

    sched_fini();
    
    ecs_fini(world);
}
