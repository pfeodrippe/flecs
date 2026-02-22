#ifndef CONCURRENCY_H
#define CONCURRENCY_H

/* This generated file contains includes for project dependencies */
#include <concurrency/bake_config.h>
#include <stdio.h>
#include <pthread.h>

/* Include our scheduler */
#include "sched.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Common types used in concurrency tests */
typedef struct Position {
    float x;
    float y;
} Position;

typedef struct Velocity {
    float x;
    float y;
} Velocity;

#ifdef __cplusplus
}
#endif

#endif /* CONCURRENCY_H */
