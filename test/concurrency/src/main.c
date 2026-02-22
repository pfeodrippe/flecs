
/* A friendly warning from bake.test
 * ----------------------------------------------------------------------------
 * This file is generated. To add/remove testcases modify the 'project.json' of
 * the test project. ANY CHANGE TO THIS FILE IS LOST AFTER (RE)BUILDING!
 * ----------------------------------------------------------------------------
 */

#include <concurrency.h>

// Testsuite 'MonitorAllocRace'
void MonitorAllocRace_double_alloc_leak(void);

// Testsuite 'DirtyStateRace'
void DirtyStateRace_lost_increment(void);
void DirtyStateRace_correct_interleaving(void);

// Testsuite 'EnsureDirectWriteRace'
void EnsureDirectWriteRace_concurrent_raw_ptrs(void);
void EnsureDirectWriteRace_sequential_writes(void);

// Testsuite 'TimeSpentRace'
void TimeSpentRace_lost_time_measurement(void);
void TimeSpentRace_correct_interleaving(void);

// Testsuite 'EvalCountRace'
void EvalCountRace_lost_eval_count(void);
void EvalCountRace_correct_interleaving(void);

// Testsuite 'MonitorSyncRace'
void MonitorSyncRace_concurrent_writes(void);
void MonitorSyncRace_stale_monitor_value(void);

// Testsuite 'OrderBySortRace'
void OrderBySortRace_concurrent_sort(void);
void OrderBySortRace_lost_match_count(void);

bake_test_case MonitorAllocRace_testcases[] = {
    {
        "double_alloc_leak",
        MonitorAllocRace_double_alloc_leak
    }
};

bake_test_case DirtyStateRace_testcases[] = {
    {
        "lost_increment",
        DirtyStateRace_lost_increment
    },
    {
        "correct_interleaving",
        DirtyStateRace_correct_interleaving
    }
};

bake_test_case EnsureDirectWriteRace_testcases[] = {
    {
        "concurrent_raw_ptrs",
        EnsureDirectWriteRace_concurrent_raw_ptrs
    },
    {
        "sequential_writes",
        EnsureDirectWriteRace_sequential_writes
    }
};

bake_test_case TimeSpentRace_testcases[] = {
    {
        "lost_time_measurement",
        TimeSpentRace_lost_time_measurement
    },
    {
        "correct_interleaving",
        TimeSpentRace_correct_interleaving
    }
};

bake_test_case EvalCountRace_testcases[] = {
    {
        "lost_eval_count",
        EvalCountRace_lost_eval_count
    },
    {
        "correct_interleaving",
        EvalCountRace_correct_interleaving
    }
};

bake_test_case MonitorSyncRace_testcases[] = {
    {
        "concurrent_writes",
        MonitorSyncRace_concurrent_writes
    },
    {
        "stale_monitor_value",
        MonitorSyncRace_stale_monitor_value
    }
};

bake_test_case OrderBySortRace_testcases[] = {
    {
        "concurrent_sort",
        OrderBySortRace_concurrent_sort
    },
    {
        "lost_match_count",
        OrderBySortRace_lost_match_count
    }
};

static bake_test_suite suites[] = {
    {
        "MonitorAllocRace",
        NULL,
        NULL,
        1,
        MonitorAllocRace_testcases
    },
    {
        "DirtyStateRace",
        NULL,
        NULL,
        2,
        DirtyStateRace_testcases
    },
    {
        "EnsureDirectWriteRace",
        NULL,
        NULL,
        2,
        EnsureDirectWriteRace_testcases
    },
    {
        "TimeSpentRace",
        NULL,
        NULL,
        2,
        TimeSpentRace_testcases
    },
    {
        "EvalCountRace",
        NULL,
        NULL,
        2,
        EvalCountRace_testcases
    },
    {
        "MonitorSyncRace",
        NULL,
        NULL,
        2,
        MonitorSyncRace_testcases
    },
    {
        "OrderBySortRace",
        NULL,
        NULL,
        2,
        OrderBySortRace_testcases
    }
};

int main(int argc, char *argv[]) {
    return bake_test_run("concurrency", argc, argv, suites, 7);
}
