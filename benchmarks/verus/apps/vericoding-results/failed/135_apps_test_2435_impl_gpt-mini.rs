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
/* helper modified by LLM (iteration 3): compute result per case without tracked vars */
fn compute_result_for_case(n: i8, x: i8, operations: Vec<(i8, i8)>) -> i8
    ensures
        compute_final_bounds(x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)).1 - compute_final_bounds(x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)).0 + 1) == result as int,
        compute_final_bounds(x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)).0) <= x as int <= compute_final_bounds(x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)).1),
        1 <= result as int,
{
    let mut min_i8: i8 = x;
    let mut max_i8: i8 = x;
    let mut idx: usize = 0usize;
    while idx < operations.len()
        invariant
            0 <= idx as int <= operations.len() as int,
        decreases operations.len() as int - idx as int
    {
        let (l8, r8) = operations[idx];
        let l = l8 as int;
        let r = r8 as int;
        if (min_i8 as int >= l && min_i8 as int <= r) || (max_i8 as int >= l && max_i8 as int <= r) {
            if l8 < min_i8 { min_i8 = l8; }
            if r8 > max_i8 { max_i8 = r8; }
        }
        idx += 1;
    }
    (max_i8 - min_i8 + 1) as i8
}

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8, Vec<(i8, i8)>)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))))
    ensures valid_results(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate test cases and call helper */
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    while i < test_cases.len()
        invariant
            0 <= i as int <= test_cases.len() as int,
            results.len() == i,
            forall|k: int| 0 <= k < i as int ==> {
                let tc = test_cases@[k];
                let (n8, x8, ops_vec) = tc;
                let seq_ops = ops_vec@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int));
                let fb = compute_final_bounds(x8 as int, seq_ops);
                results@[k] as int == fb.1 - fb.0 + 1
            },
        decreases test_cases.len() as int - i as int
    {
        let (n8, x8, ops_vec) = test_cases[i];
        let r = compute_result_for_case(n8, x8, ops_vec);
        results.push(r);
        i += 1;
    }
    results
}

// </vc-code>


}

fn main() {}