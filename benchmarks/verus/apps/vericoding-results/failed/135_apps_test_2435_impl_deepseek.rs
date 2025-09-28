// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(test_cases: Seq<(int, int, Seq<(int, int)>)>) -> bool {
    test_cases.len() >= 0 &&
    forall|i: int| 0 <= i < test_cases.len() ==> #[trigger] test_cases[i].0 >= 1 && {
        let (n, x, operations) = test_cases[i];
        n >= 1 && 1 <= x <= n && operations.len() >= 0 &&
        forall|j: int| 0 <= j < operations.len() ==> #[trigger] operations[j].0 >= 1 && {
            let (l, r) = operations[j];
            1 <= l <= r <= n
        }
    }
}

spec fn compute_final_bounds(x: int, operations: Seq<(int, int)>) -> (int, int)
    recommends forall|j: int| 0 <= j < operations.len() ==> #[trigger] operations[j].0 <= operations[j].1
{
    compute_final_bounds_helper(x, x, operations, 0)
}

spec fn valid_results(test_cases: Seq<(int, int, Seq<(int, int)>)>, results: Seq<int>) -> bool
    recommends valid_input(test_cases)
{
    results.len() == test_cases.len() &&
    forall|i: int| 0 <= i < test_cases.len() ==> #[trigger] test_cases[i].0 >= 1 && {
        let (n, x, operations) = test_cases[i];
        let final_bounds = compute_final_bounds(x, operations);
        results[i] == final_bounds.1 - final_bounds.0 + 1 &&
        final_bounds.0 <= x <= final_bounds.1 &&
        results[i] >= 1 &&
        1 <= final_bounds.0 <= final_bounds.1 <= n
    }
}

spec fn compute_final_bounds_helper(min_pos: int, max_pos: int, operations: Seq<(int, int)>, index: int) -> (int, int)
    decreases operations.len() - index
{
    if index >= operations.len() {
        (min_pos, max_pos)
    } else {
        let (l, r) = operations[index];
        let new_min = if min_pos >= l && min_pos <= r || max_pos >= l && max_pos <= r {
            if l < min_pos { l } else { min_pos }
        } else { min_pos };
        let new_max = if min_pos >= l && min_pos <= r || max_pos >= l && max_pos <= r {
            if r > max_pos { r } else { max_pos }
        } else { max_pos };
        compute_final_bounds_helper(new_min, new_max, operations, index + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add requires for x bounds and fix measurement */
fn compute_final_bounds_executable(x: i8, operations: Vec<(i8, i8)>) -> (i8, i8)
    requires
        1 <= x <= i8::MAX,
        operations@.len() >= 0,
        forall|j: int| 0 <= j < operations@.len() ==> #[trigger] operations@[j].0 <= operations@[j].1,
        forall|j: int| 0 <= j < operations@.len() ==> 1 <= operations@[j].0 <= i8::MAX && 1 <= operations@[j].1 <= i8::MAX,
    ensures
        result.0 <= x <= result.1,
        result.1 - result.0 + 1 >= 1,
{
    let mut min_pos = x;
    let mut max_pos = x;
    let mut index: usize = 0;
    while index < operations.len()
        invariant
            index <= operations@.len(),
            min_pos <= max_pos,
            min_pos <= x <= max_pos,
            min_pos >= 1,
            max_pos <= i8::MAX,
        decreases operations.len() - index,
    {
        let (l, r) = operations[index];
        if (min_pos >= l && min_pos <= r) || (max_pos >= l && max_pos <= r) {
            if l < min_pos {
                min_pos = l;
            }
            if r > max_pos {
                max_pos = r;
            }
        }
        index += 1;
    }
    (min_pos, max_pos)
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8, Vec<(i8, i8)>)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))))
    ensures valid_results(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix result handling and ensure proper bounds */
    let len = test_cases.len();
    let mut results = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant
            results@.len() == i,
            i <= len,
    {
        let (n, x, operations_vec) = test_cases[i].clone();
        let final_bounds = compute_final_bounds_executable(x, operations_vec);
        let result_val = (final_bounds.1 as i32 - final_bounds.0 as i32 + 1) as i8;
        results.push(result_val);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}