/**
 * @file MultiStageMerge.c
 * @brief Test suite for multi-stage command merge race.
 *
 * Bug: This models a DESIGN-LEVEL issue: silent data loss when cross-stage
 * conflicts occur. Stage 0 can delete an entity, causing all of Stage 1's
 * commands for that entity to be silently discarded — no warning, no error.
 *
 * The key issue is that worker stages observe entity E as alive during
 * readonly phase and enqueue commands. But during merge, if an earlier
 * stage deleted E, later stage commands are silently dropped.
 *
 * TLA+ spec: MultiStageMerge.tla
 * Location: src/commands.c:1177-1214 (flecs_defer_end merge loop)
 */

#include <concurrency.h>

/* Shared test state */
typedef struct {
    ecs_world_t *world;
    ecs_world_t *stages[3];
    ecs_entity_t entity;
    ecs_id_t component_id;
    int commands_discarded;
} MergeTestData;

/* Thread function that adds a component */
static void worker_add_fn(int thread_id, void *data) {
    MergeTestData *td = (MergeTestData *)data;
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Add component - this command may be discarded if entity is deleted */
    ecs_add_id(stage, td->entity, td->component_id);
}

/* Thread function that deletes the entity */
static void worker_delete_fn(int thread_id, void *data) {
    MergeTestData *td = (MergeTestData *)data;
    ecs_world_t *stage = td->stages[thread_id];
    
    /* Delete entity - causes later stage commands to be discarded */
    ecs_delete(stage, td->entity);
}

/**
 * Test: silent_data_loss
 *
 * Stage 0 deletes entity, Stage 1 adds component. Stage 1's command
 * is silently discarded during merge with no warning.
 */
void MultiStageMerge_silent_data_loss(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    
    ecs_entity_t e = ecs_new(world);
    ecs_set(world, e, Position, {1.0f, 1.0f});
    
    MergeTestData td = {
        .world = world,
        .entity = e,
        .component_id = ecs_id(Velocity),
        .commands_discarded = 0
    };
    td.stages[1] = ecs_get_stage(world, 0);
    td.stages[2] = ecs_get_stage(world, 1);
    
    /* Begin deferred mode */
    ecs_defer_begin(world);
    
    /* Stage 0 deletes, Stage 1 adds (to the now-deleted entity) */
    ecs_delete(td.stages[1], e);
    ecs_add(td.stages[2], e, Velocity);
    
    /* End deferred mode - triggers merge */
    ecs_defer_end(world);
    
    /* The add command was silently discarded because entity was deleted
     * by an earlier stage. This is the "bug" (design issue). */
    test_assert(!ecs_is_alive(world, e));
    
    ecs_fini(world);
}

/**
 * Test: merge_order_matters
 *
 * Demonstrates that the merge order (stage 0 before stage 1) determines
 * which commands take effect when there are cross-stage conflicts.
 * This shows that if Stage 0 modifies an entity, Stage 1's earlier
 * observation may be invalidated.
 */
void MultiStageMerge_merge_order_matters(void) {
    ecs_world_t *world = ecs_init();
    ecs_set_stage_count(world, 2);
    
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    
    ecs_entity_t e = ecs_new(world);
    ecs_set(world, e, Position, {1.0f, 1.0f});
    
    ecs_world_t *stage0 = ecs_get_stage(world, 0);
    ecs_world_t *stage1 = ecs_get_stage(world, 1);
    
    /* Begin deferred mode on both stages */
    ecs_defer_begin(world);
    
    /* Stage 0: Delete the entity */
    ecs_delete(stage0, e);
    
    /* Stage 1: Add a component (doesn't know entity will be deleted) */
    ecs_add(stage1, e, Velocity);
    
    /* End deferred mode - triggers merge.
     * Stage 0 commands merge first (delete), then Stage 1 (add).
     * Stage 1's add is discarded because entity was deleted by Stage 0. */
    ecs_defer_end(world);
    
    /* Entity should be deleted (Stage 0's delete wins) */
    test_assert(!ecs_is_alive(world, e));
    
    ecs_fini(world);
}
