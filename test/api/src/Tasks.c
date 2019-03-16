#include <include/api.h>

void Task(EcsRows *rows) {
    
    ProbeSystem(rows);

    int i;
    for (i = rows->begin; i < rows->end; i ++) {
    }
}

void Tasks_no_components() {
    EcsWorld *world = ecs_init();

    ECS_SYSTEM(world, Task, EcsOnFrame, 0);

    SysTestData ctx = {0};
    ecs_set_context(world, &ctx);

    ecs_progress(world, 1);

    test_int(ctx.count, 0);
    test_int(ctx.invoked, 1);
    test_int(ctx.column_count, 0);

    ecs_fini(world);
}

void Tasks_one_tag() {
    EcsWorld *world = ecs_init();

    ECS_SYSTEM(world, Task, EcsOnFrame, SYSTEM.EcsHidden);

    SysTestData ctx = {0};
    ecs_set_context(world, &ctx);

    ecs_progress(world, 1);

    test_int(ctx.count, 0);
    test_int(ctx.invoked, 1);
    test_int(ctx.column_count, 1);
    test_int(ctx.c[0][0], EEcsHidden);

    ecs_fini(world);
}

void Tasks_from_system() {
    // Implement testcase
}

void Tasks_on_remove_no_components() {
    // Implement testcase
}

void Tasks_on_remove_one_tag() {
    // Implement testcase
}

void Tasks_on_remove_from_system() {
    // Implement testcase
}
