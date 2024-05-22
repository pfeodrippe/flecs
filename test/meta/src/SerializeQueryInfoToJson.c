#include <meta.h>

void SerializeQueryInfoToJson_1_tag(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_component(void) {
    ecs_world_t *world = ecs_init();

    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_query_t *q = ecs_query(world, {
        .expr = "Position"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":true, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Position\", \"symbol\":\"Position\", \"type\":true}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_pair(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Rel, (OnInstantiate, Inherit));
    ECS_ENTITY(world, Tgt, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "(Rel, Tgt)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Rel\"}, "
            "\"second\":{\"entity\":\"Tgt\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_pair_w_wildcard(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Rel, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "(Rel, *)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Rel\"}, "
            "\"second\":{\"var\":\"*\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_pair_w_any(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Rel, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "(Rel, _)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Rel\"}, "
            "\"second\":{\"var\":\"_\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);
    
    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_fixed_src(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));
    ECS_ENTITY(world, e, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(e)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"entity\":\"e\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_var_src(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo($v)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"vars\":[\"v\"], \"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"v\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_component_in(void) {
    ecs_world_t *world = ecs_init();

    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_query_t *q = ecs_query(world, {
        .expr = "[in] Position"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"in\", \"has_data\":true, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Position\", \"symbol\":\"Position\", \"type\":true}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_component_inout(void) {
    ecs_world_t *world = ecs_init();

    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_query_t *q = ecs_query(world, {
        .expr = "[inout] Position"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"inout\", \"has_data\":true, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Position\", \"symbol\":\"Position\", \"type\":true}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_component_out(void) {
    ecs_world_t *world = ecs_init();

    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_query_t *q = ecs_query(world, {
        .expr = "[out] Position"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"out\", \"has_data\":true, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Position\", \"symbol\":\"Position\", \"type\":true}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_component_none(void) {
    ecs_world_t *world = ecs_init();

    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_query_t *q = ecs_query(world, {
        .expr = "[none] Position"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"none\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Position\", \"symbol\":\"Position\", \"type\":true}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_not(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "!Foo"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"none\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"not\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_2_tags_or(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));
    ECS_ENTITY(world, Bar, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo || Bar"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"or\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}, "
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Bar\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_optional(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "?Foo"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"optional\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.IsA\", \"symbol\":\"EcsIsA\"}, "
            "\"flags\":[\"self\", \"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_self(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(self)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"flags\":[\"self\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_self_dont_inherit(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, DontInherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(self)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"flags\":[\"self\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_up(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(up)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.ChildOf\", \"symbol\":\"EcsChildOf\"}, "
            "\"flags\":[\"up\"]}]}}");
    ecs_os_free(json);

    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_1_tag_cascade(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(cascade)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":""{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"var\":\"this\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"trav\":{\"entity\":\"flecs.core.ChildOf\", \"symbol\":\"EcsChildOf\"}, "
            "\"flags\":[\"cascade\"]}]}}");
    ecs_os_free(json);
    
    ecs_query_fini(q);

    ecs_fini(world);
}

void SerializeQueryInfoToJson_0_term(void) {
    ecs_world_t *world = ecs_init();

    ECS_ENTITY(world, Foo, (OnInstantiate, Inherit));

    ecs_query_t *q = ecs_query(world, {
        .expr = "Foo(0)"
    });

    test_assert(q != NULL);

    ecs_iter_t it = ecs_query_iter(world, q);
    ecs_iter_to_json_desc_t desc = {
        .serialize_query_info = true,
        .dont_serialize_results = true
    };

    char *json = ecs_iter_to_json(&it, &desc);
    test_str(json, "{\"query_info\":{\"terms\":["
        "{\"inout\":\"default\", \"has_data\":false, \"can_inherit\":true, \"oper\":\"and\", "
            "\"src\":{\"entity\":\"0\"}, "
            "\"first\":{\"entity\":\"Foo\"}, "
            "\"flags\":[]}]}}");
    ecs_os_free(json);
    
    ecs_query_fini(q);

    ecs_fini(world);
}
