/**
 * @file EntityIndexRace.c
 * @brief Test suite for entity index race conditions.
 *
 * Bug: When multiple threads call flecs_entity_index_new_id concurrently
 * (via ecs_new), with NO synchronization:
 *   - Both read alive_count, both return dense[alive_count], both increment
 *     Result: same entity ID returned to both threads
 *   - Both read max_id, both get same ID, both increment
 *     Result: same entity ID allocated twice, dense array corruption
 *
 * In debug builds, ecs_assert guards entity creation. In RELEASE builds,
 * this assert is stripped — leaving zero protection.
 *
 * TLA+ spec: EntityIndexRace.tla
 * Location: src/storage/entity_index.c (flecs_entity_index_new_id)
 */

#include <concurrency.h>

/* Setup function to enable test_expect_abort functionality */
void EntityIndexRace_setup(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_api;
    os_api.abort_ = test_abort;
    ecs_os_set_api(&os_api);
}

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_entity_t created[3];  /* Entities created by each thread */
} EntityIndexTestData;

/* Thread function that creates a new entity */
static void worker_new_fn(int thread_id, void *data) {
    EntityIndexTestData *td = (EntityIndexTestData *)data;
    
    /* Create new entity - this calls flecs_entity_index_new_id internally.
     * Note: This is racy without the world lock, but we're demonstrating
     * the bug that exists when user code bypasses the lock. */
    td->created[thread_id] = ecs_new(td->world);
}

/**
 * Test: duplicate_entity_allocation
 *
 * Forces both threads to read alive_count before either writes,
 * potentially causing duplicate entity ID allocation.
 */
void EntityIndexRace_duplicate_entity_allocation(void) {
    test_expect_abort();

    ecs_world_t *world = ecs_init();
    
    /* Pre-create some entities so there's recycling potential */
    ecs_entity_t e1 = ecs_new(world);
    ecs_entity_t e2 = ecs_new(world);
    ecs_delete(world, e1);
    ecs_delete(world, e2);
    
    EntityIndexTestData td = { .world = world };
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_new_fn,
        .thread_data = &td,
        .timeout_ms = 5000,
        .schedule_len = 6,
        .schedule = {
            /* Recycling race: both check/read the same slot before either writes. */
            SCHED_STEP(1, "entity_index_check_recycle"),
            SCHED_STEP(2, "entity_index_check_recycle"),
            SCHED_STEP(1, "entity_index_recycle_read"),
            SCHED_STEP(2, "entity_index_recycle_read"),
            SCHED_STEP(1, "entity_index_recycle_write"),
            SCHED_STEP(2, "entity_index_recycle_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    if (result == 0) {
        /* Bug final state: both threads returned the same entity id. */
        test_assert(td.created[1] != 0);
        test_assert(td.created[2] != 0);
        test_assert(td.created[1] == td.created[2]);
    }
    
    ecs_fini(world);
}

/**
 * Test: max_id_race
 *
 * Forces both threads to read max_id before either writes (creation path),
 * potentially causing the same max_id to be allocated twice.
 *
 * This test intentionally demonstrates a REAL BUG in Flecs when
 * ecs_new is called concurrently without proper synchronization.
 * In debug builds, this triggers an assertion failure:
 *   "new entity X id already in use"
 * This proves the TLA+ spec correctly identified the race condition.
 *
 * The test expects an abort - this is SUCCESS (proves the bug exists).
 */
void EntityIndexRace_max_id_race(void) {
    /* Tell test framework we expect this test to abort */
    test_expect_abort();
    
    ecs_world_t *world = ecs_init();
    
    /* Don't create/delete entities - force the creation (not recycle) path */
    
    EntityIndexTestData td = { .world = world };
    
    sched_init();
    
    sched_config_t config = {
        .num_threads = 2,
        .thread_fn = worker_new_fn,
        .thread_data = &td,
        .timeout_ms = 2000,  /* Short timeout */
        .schedule_len = 4,
        .schedule = {
            /* Creation race: both read max_id, both write max_id+1 */
            SCHED_STEP(1, "entity_index_maxid_read"),
            SCHED_STEP(2, "entity_index_maxid_read"),
            SCHED_STEP(1, "entity_index_maxid_write"),
            SCHED_STEP(2, "entity_index_maxid_write"),
            SCHED_END
        }
    };
    
    int result = sched_run(&config);
    sched_fini();
    
    /* If no abort happened, still require bug outcome (duplicate id). */
    if (result == 0) {
        /* Bug final state: both threads returned the same entity id. */
        test_assert(td.created[1] != 0);
        test_assert(td.created[2] != 0);
        test_assert(td.created[1] == td.created[2]);
    }
    
    /* On non-abort path we already validated duplicate allocation. */
    ecs_fini(world);
}
