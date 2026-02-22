# Controlled Scheduling for Deterministic Race Reproduction

## Goal

Reproduce the race conditions found via TLA+ model checking in actual C unit tests
using **controlled thread scheduling** to force specific interleavings.

## The Problem

Race conditions are non-deterministic. Running a test 1000 times might not trigger
the bug even once. But TLC showed us the **exact interleaving** that causes each bug.

For example, Bug 7 (monitor allocation leak) requires:
```
Thread A: check(_monitor == NULL) → TRUE
Thread B: check(_monitor == NULL) → TRUE  (before A writes!)
Thread A: allocate monitor_A
Thread B: allocate monitor_B
Thread A: write _monitor = monitor_A
Thread B: write _monitor = monitor_B  (leak monitor_A!)
```

We need to **force** this interleaving deterministically.

## Approach: Barrier-Based Scheduling

### Core Idea

Insert **synchronization barriers** at the race-prone code points. Use a **scheduler**
that controls which thread proceeds through each barrier and in what order.

```
                    ┌─────────────────┐
                    │    Scheduler    │
                    │  (main thread)  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
              ▼              ▼              ▼
         ┌────────┐    ┌────────┐    ┌────────┐
         │Thread 1│    │Thread 2│    │Thread 3│
         └────┬───┘    └────┬───┘    └────┬───┘
              │              │              │
              ▼              ▼              ▼
         barrier(1)    barrier(1)    barrier(1)
              │              │              │
              ├──────────────┼──────────────┤
              │     wait for scheduler      │
              ├──────────────┼──────────────┤
              │              │              │
```

### Implementation Components

#### 1. Schedule Definition

A **schedule** is a sequence of (thread_id, barrier_id) pairs that defines the
exact order threads should execute:

```c
typedef struct {
    int thread_id;      // Which thread to release
    const char *point;  // Named barrier point (e.g., "check", "alloc", "write")
} sched_step_t;

// Bug 7 reproduction schedule:
sched_step_t bug7_schedule[] = {
    {1, "check"},   // Thread 1 checks _monitor == NULL
    {2, "check"},   // Thread 2 checks _monitor == NULL (both see NULL!)
    {1, "alloc"},   // Thread 1 allocates
    {2, "alloc"},   // Thread 2 allocates
    {1, "write"},   // Thread 1 writes _monitor
    {2, "write"},   // Thread 2 writes _monitor (overwrites, leaks!)
    {0, NULL}       // End
};
```

#### 2. Barrier Implementation

Each thread calls `sched_barrier(point_name)` at instrumented locations:

```c
void sched_barrier(const char *point) {
    int my_thread = get_current_thread_id();
    
    pthread_mutex_lock(&sched_mutex);
    
    // Signal scheduler that we've arrived at this point
    thread_state[my_thread] = point;
    pthread_cond_signal(&sched_cond);
    
    // Wait until scheduler tells us to proceed
    while (!thread_proceed[my_thread]) {
        pthread_cond_wait(&thread_cond[my_thread], &sched_mutex);
    }
    thread_proceed[my_thread] = false;
    
    pthread_mutex_unlock(&sched_mutex);
}
```

#### 3. Scheduler Loop

The scheduler (running in the test's main thread) executes the schedule:

```c
void run_schedule(sched_step_t *schedule) {
    for (int i = 0; schedule[i].point != NULL; i++) {
        int tid = schedule[i].thread_id;
        const char *point = schedule[i].point;
        
        pthread_mutex_lock(&sched_mutex);
        
        // Wait until target thread reaches the barrier point
        while (strcmp(thread_state[tid], point) != 0) {
            pthread_cond_wait(&sched_cond, &sched_mutex);
        }
        
        // Release the thread
        thread_proceed[tid] = true;
        pthread_cond_signal(&thread_cond[tid]);
        
        pthread_mutex_unlock(&sched_mutex);
    }
}
```

#### 4. Instrumentation Points

We need to add barrier calls at the race-prone locations. Two approaches:

**A. Source Code Modification (invasive but precise)**

Add `SCHED_BARRIER("point_name")` macros directly in Flecs source:

```c
// In change_detection.c:48-93
bool flecs_query_get_match_monitor(...) {
    SCHED_BARRIER("check");           // <-- Added
    if (match->_monitor) {
        return false;
    }

    SCHED_BARRIER("alloc");           // <-- Added
    int32_t *monitor = flecs_balloc(&cache->allocators.monitors);
    // ...
    
    SCHED_BARRIER("write");           // <-- Added
    match->_monitor = monitor;
    return true;
}
```

**B. Function Interposition (less invasive)**

Use `LD_PRELOAD` or linker tricks to intercept specific functions and add
barriers around them. Works for `flecs_balloc`, etc.

## Implementation Plan

### Phase 1: Create the Scheduler Framework

1. Create `test/concurrency/sched.h` - header with scheduler API
2. Create `test/concurrency/sched.c` - scheduler implementation
3. Create `test/concurrency/project.json` - bake build config

### Phase 2: Instrument Flecs for Testing

1. Add `FLECS_SCHED_TESTING` compile flag
2. Add `SCHED_BARRIER()` macros that are no-ops unless flag is set
3. Instrument `flecs_query_get_match_monitor` (Bug 7)
4. Instrument `flecs_defer_ensure` (Bug 1)
5. Instrument `flecs_query_mark_fixed_fields_dirty` (Bug 3)

### Phase 3: Write Reproduction Tests

For each bug, create a test that:
1. Sets up the minimal Flecs world state
2. Spawns worker threads that hit the instrumented code
3. Runs the bug-triggering schedule
4. Asserts the bug occurred (memory leak, data corruption, etc.)

### Phase 4: Verify

1. Run tests with controlled scheduling → bugs reproduced deterministically
2. Run tests without scheduling → bugs may or may not appear (non-deterministic)
3. Apply fixes to Flecs
4. Run tests again → bugs no longer reproducible

## Bugs to Reproduce

| Bug # | Location | Barrier Points | Detection |
|-------|----------|----------------|-----------|
| 1 | `commands.c:399-459` | get_existing, return_ptr | Two threads get same raw pointer |
| 3 | `change_detection.c:526` | read_dirty, write_dirty | dirty_state value lower than expected |
| 5 | `change_detection.c:531-580` | enter_sync, write_monitor | Concurrent monitor writes |
| 6 | `order_by.c:228-316` | check_dirty, sort_table, inc_count | Concurrent sorting, lost count |
| 7 | `change_detection.c:48-93` | check, alloc, write | Memory leak (alloc count > 1) |

## Alternative: ThreadSanitizer + Stress Testing

If controlled scheduling is too invasive, we can use:

1. **ThreadSanitizer (TSan)**: Compile Flecs with `-fsanitize=thread`
2. **Stress loop**: Run the multi-threaded scenario many times
3. **TSan detects**: Reports the race when it happens

```bash
# Compile with TSan
clang -fsanitize=thread -g -O1 -o test_race test_race.c flecs.c

# Run many times
for i in {1..1000}; do ./test_race || break; done
```

TSan is probabilistic but requires no source changes. It can detect races but
doesn't guarantee reproduction on every run.

## Files to Create

```
test/concurrency/
├── sched.h              # Scheduler API
├── sched.c              # Scheduler implementation  
├── project.json         # Bake build config
└── src/
    ├── test_bug1.c      # ecs_ensure race test
    ├── test_bug3.c      # dirty_state race test
    ├── test_bug5.c      # monitor sync race test
    ├── test_bug6.c      # order_by race test
    └── test_bug7.c      # monitor alloc race test
```

## References

- [CHESS: Systematic Concurrency Testing](https://www.microsoft.com/en-us/research/project/chess-find-and-reproduce-heisenbugs-in-concurrent-programs/)
- [PCT: Probabilistic Concurrency Testing](https://www.microsoft.com/en-us/research/publication/a-randomized-scheduler-with-probabilistic-guarantees-of-finding-bugs/)
- [ThreadSanitizer](https://clang.llvm.org/docs/ThreadSanitizer.html)
- [rr: Record and Replay](https://rr-project.org/)
