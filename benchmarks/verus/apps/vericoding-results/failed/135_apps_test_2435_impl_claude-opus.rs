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
/* helper modified by LLM (iteration 2): Fixed index parameter types from nat to int for consistency */
proof fn lemma_compute_bounds_properties(x: int, operations: Seq<(int, int)>, index: int)
    requires
        forall|j: int| 0 <= j < operations.len() ==> #[trigger] operations[j].0 <= operations[j].1,
        0 <= index <= operations.len(),
    ensures
        compute_final_bounds_helper(x, x, operations, index).0 <= x,
        compute_final_bounds_helper(x, x, operations, index).1 >= x,
        compute_final_bounds_helper(x, x, operations, index).0 <= compute_final_bounds_helper(x, x, operations, index).1,
    decreases operations.len() - index
{
    if index >= operations.len() {
        assert(compute_final_bounds_helper(x, x, operations, index) == (x, x));
    } else {
        lemma_compute_bounds_properties(x, operations, index + 1);
    }
}

proof fn lemma_bounds_stay_valid(n: int, x: int, operations: Seq<(int, int)>, index: int, min_pos: int, max_pos: int)
    requires
        1 <= x <= n,
        forall|j: int| 0 <= j < operations.len() ==> 1 <= operations[j].0 <= operations[j].1 <= n,
        0 <= index <= operations.len(),
        1 <= min_pos <= max_pos <= n,
        min_pos <= x <= max_pos,
    ensures
        compute_final_bounds_helper(min_pos, max_pos, operations, index).0 >= 1,
        compute_final_bounds_helper(min_pos, max_pos, operations, index).1 <= n,
        compute_final_bounds_helper(min_pos, max_pos, operations, index).0 <= compute_final_bounds_helper(min_pos, max_pos, operations, index).1,
    decreases operations.len() - index
{
    if index >= operations.len() {
        assert(compute_final_bounds_helper(min_pos, max_pos, operations, index) == (min_pos, max_pos));
    } else {
        let (l, r) = operations[index];
        let overlaps = min_pos >= l && min_pos <= r || max_pos >= l && max_pos <= r;
        let new_min = if overlaps { if l < min_pos { l } else { min_pos } } else { min_pos };
        let new_max = if overlaps { if r > max_pos { r } else { max_pos } } else { max_pos };
        assert(1 <= new_min <= new_max <= n);
        lemma_bounds_stay_valid(n, x, operations, index + 1, new_min, new_max);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8, Vec<(i8, i8)>)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))))
    ensures valid_results(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed index type from nat to int in invariant */
    let mut results = Vec::new();
    let mut i = 0;
    
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] results[j] as int == compute_final_bounds(test_cases[j].1 as int, test_cases[j].2@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int))).1 - compute_final_bounds(test_cases[j].1 as int, test_cases[j].2@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int))).0 + 1,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] results[j] as int <= test_cases[j].0 as int,
    {
        let (n, x, operations) = test_cases[i];
        let mut min_pos: i8 = x;
        let mut max_pos: i8 = x;
        let mut j = 0;
        
        while j < operations.len()
            invariant
                0 <= j <= operations.len(),
                1 <= min_pos as int <= max_pos as int <= n as int,
                min_pos as int <= x as int <= max_pos as int,
                (min_pos as int, max_pos as int) == compute_final_bounds_helper(x as int, x as int, operations@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int)), j as int),
        {
            let (l, r) = operations[j];
            if (min_pos >= l && min_pos <= r) || (max_pos >= l && max_pos <= r) {
                if l < min_pos {
                    min_pos = l;
                }
                if r > max_pos {
                    max_pos = r;
                }
            }
            j = j + 1;
        }
        
        let result: i8 = max_pos - min_pos + 1;
        proof {
            lemma_compute_bounds_properties(x as int, operations@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int)), 0);
            lemma_bounds_stay_valid(n as int, x as int, operations@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int)), 0, x as int, x as int);
            assert(compute_final_bounds(x as int, operations@.map(|k: int, op: (i8, i8)| (op.0 as int, op.1 as int))) == (min_pos as int, max_pos as int));
        }
        
        results.push(result);
        i = i + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}