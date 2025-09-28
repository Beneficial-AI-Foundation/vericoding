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
/* helper modified by LLM (iteration 4): Fixed compilation error by naming the return value 'res' and using 'res' in ensures instead of 'result' to enable access to return tuple fields. */
fn exec_final_bounds(n: i8, x: i8, operations: Vec<(i8, i8)>) -> (res: (i8, i8))
    requires
        n >= 1,
        1 <= x <= n,
        operations@.len() >= 0,
        forall |j: int| 0 <= j < operations@.len() ==> {
            let (l, r) = operations@[j];
            1 <= l as int <= r as int <= n as int
        }
    ensures
        compute_final_bounds(x as int, operations@.map(|j: int, p: (i8, i8)| (p.0 as int, p.1 as int))) == (res.0 as int, res.1 as int)
{
    let mut min_pos = x;
    let mut max_pos = x;
    let mut index: usize = 0;
    while index < operations.len()
        invariant
            min_pos as int <= x as int <= max_pos as int,
            compute_final_bounds_helper(min_pos as int, max_pos as int, operations@.map(|j: int, p: (i8, i8)| (p.0 as int, p.1 as int)), index as int) == (min_pos as int, max_pos as int),
            0 <= (index as int) <= operations@.len()
        decreases operations@.len() - (index as int)
    {
        let (l_, r_) = operations[index];
        if (l_ <= min_pos && min_pos <= r_) || (l_ <= max_pos && max_pos <= r_) {
            if l_ < min_pos { min_pos = l_; }
            if r_ > max_pos { max_pos = r_; }
        }
        index = index + 1;
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
/* code modified by LLM (iteration 5): Fixed compilation error by borrowing the tuple from vector to avoid moving non-Copy type. */
{
    let mut results = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            0 <= (i as int) <= test_cases@.len(),
            results@.len() == (i as int)
    {
        let tc = &test_cases[i];
        let n = tc.0;
        let x = tc.1;
        let ops = tc.2.clone();
        let (min_p, max_p) = exec_final_bounds(n, x, ops);
        let span = max_p - min_p + 1;
        results.push(span);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}