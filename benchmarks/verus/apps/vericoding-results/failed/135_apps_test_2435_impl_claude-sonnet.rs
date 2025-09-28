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
/* helper modified by LLM (iteration 5): Fixed lemma syntax by adding exec keyword */
exec fn lemma_compute_final_bounds_helper_properties(min_pos: int, max_pos: int, operations: Seq<(int, int)>, index: int)
    requires
        min_pos <= max_pos,
        forall|j: int| 0 <= j < operations.len() ==> operations[j].0 <= operations[j].1,
        0 <= index <= operations.len()
    ensures
        {
            let result = compute_final_bounds_helper(min_pos, max_pos, operations, index);
            result.0 <= result.1 && result.0 <= min_pos && result.1 >= max_pos
        }
    decreases operations.len() - index
{
    if index >= operations.len() {
        // Base case
    } else {
        let (l, r) = operations[index];
        let overlaps = min_pos >= l && min_pos <= r || max_pos >= l && max_pos <= r;
        let new_min = if overlaps {
            if l < min_pos { l } else { min_pos }
        } else { min_pos };
        let new_max = if overlaps {
            if r > max_pos { r } else { max_pos }
        } else { max_pos };
        lemma_compute_final_bounds_helper_properties(new_min, new_max, operations, index + 1);
    }
}

fn compute_final_bounds_exec(x: i8, operations: &Vec<(i8, i8)>) -> (min_pos: i8, max_pos: i8)
    requires
        forall|j: int| 0 <= j < operations@.len() ==> operations@[j].0 <= operations@[j].1,
        x >= 1
    ensures
        min_pos <= max_pos,
        min_pos <= x <= max_pos,
        (min_pos as int, max_pos as int) == compute_final_bounds(x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))
{
    let mut min_pos = x;
    let mut max_pos = x;
    let mut i = 0;
    
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            min_pos <= max_pos,
            min_pos <= x <= max_pos,
            (min_pos as int, max_pos as int) == compute_final_bounds_helper(x as int, x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)), i as int)
    {
        let (l, r) = operations[i];
        let overlaps = (min_pos >= l && min_pos <= r) || (max_pos >= l && max_pos <= r);
        
        if overlaps {
            if l < min_pos {
                min_pos = l;
            }
            if r > max_pos {
                max_pos = r;
            }
        }
        
        i += 1;
    }
    
    proof {
        lemma_compute_final_bounds_helper_properties(x as int, x as int, operations@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)), 0);
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
    /* code modified by LLM (iteration 5): Fixed main implementation to properly compute final bounds */
    let mut results = Vec::new();
    let mut i = 0;
    
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            forall|k: int| 0 <= k < i ==> {
                let tc_spec = test_cases@[k as int];
                let tc_spec_converted = (tc_spec.0 as int, tc_spec.1 as int, tc_spec.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)));
                let final_bounds = compute_final_bounds(tc_spec_converted.1, tc_spec_converted.2);
                results@[k as int] as int == final_bounds.1 - final_bounds.0 + 1
            }
    {
        let (n, x, operations) = &test_cases[i];
        
        let (min_pos, max_pos) = compute_final_bounds_exec(*x, operations);
        let result = max_pos - min_pos + 1;
        
        results.push(result);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}