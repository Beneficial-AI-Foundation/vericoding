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
/* helper modified by LLM (iteration 5): Removed redundant helper section. The `compute_final_bounds_helper` function was already defined in the preamble, so it should not be redefined. */
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8, Vec<(i8, i8)>)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))))
    ensures valid_results(test_cases@.map(|i: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int)))), results@.map(|i: int, r: i8| r as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed `recursion` prover from `assert` statements as it's not a valid prover. Changed concrete variable casts to ghost variables. */
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < test_cases.len()
        invariant
            0 <= i && i <= test_cases.len(),
            results.len() == i,
            valid_results(test_cases@.subsequence(0, i).map(|k: int, tc: (i8, i8, Vec<(i8, i8)>)| (tc.0 as int, tc.1 as int, tc.2@.map(|l: int, op: (i8, i8)| (op.0 as int, op.1 as int)))), results@.map(|k: int, r: i8| r as int))
    {
        let (n_i8, x_i8, operations_vec) = &test_cases[i];
        let ghost n = *n_i8 as int;
        let ghost x = *x_i8 as int;
        let ghost operations = operations_vec@.map(|j: int, op: (i8, i8)| (op.0 as int, op.1 as int));

        let mut min_pos_concrete: i8 = *x_i8;
        let mut max_pos_concrete: i8 = *x_i8;

        let mut j = 0;
        while j < operations_vec.len()
            invariant
                0 <= j && j <= operations_vec.len(),
                1 <= min_pos_concrete as int, min_pos_concrete as int <= max_pos_concrete as int, max_pos_concrete as int <= n,
                // Ensure that the computed bounds are consistent with the helper function
                (min_pos_concrete as int, max_pos_concrete as int) == compute_final_bounds_helper(x, x, operations.subsequence(0, j), 0)
        {
            let (l_i8, r_i8) = operations_vec[j];
            let ghost l = l_i8 as int;
            let ghost r = r_i8 as int;
            
            proof {
                let ghost current_min_pos_int = min_pos_concrete as int;
                let ghost current_max_pos_int = max_pos_concrete as int;

                let (computed_min, computed_max) = compute_final_bounds_helper(x, x, operations.subsequence(0, j + 1), 0);

                let ghost new_min_calc_int = if (current_min_pos_int >= l && current_min_pos_int <= r) || (current_max_pos_int >= l && current_max_pos_int <= r) {
                    if l < current_min_pos_int { l } else { current_min_pos_int }
                } else { current_min_pos_int };
                let ghost new_max_calc_int = if (current_min_pos_int >= l && current_min_pos_int <= r) || (current_max_pos_int >= l && current_max_pos_int <= r) {
                    if r > current_max_pos_int { r } else { current_max_pos_int }
                } else { current_max_pos_int };
                
                assert(new_min_calc_int == computed_min);
                assert(new_max_calc_int == computed_max);
            }
            
            let ghost current_min_pos_int = min_pos_concrete as int;
            let ghost current_max_pos_int = max_pos_concrete as int;
            let new_min_i8: i8;
            let new_max_i8: i8;
            
            if (min_pos_concrete >= l_i8 && min_pos_concrete <= r_i8) || (max_pos_concrete >= l_i8 && max_pos_concrete <= r_i8) {
                if l_i8 < min_pos_concrete { new_min_i8 = l_i8; } else { new_min_i8 = min_pos_concrete; }
            } else { new_min_i8 = min_pos_concrete; }

            if (min_pos_concrete >= l_i8 && min_pos_concrete <= r_i8) || (max_pos_concrete >= l_i8 && max_pos_concrete <= r_i8) {
                if r_i8 > max_pos_concrete { new_max_i8 = r_i8; } else { new_max_i8 = max_pos_concrete; }
            } else { new_max_i8 = max_pos_concrete; }

            min_pos_concrete = new_min_i8;
            max_pos_concrete = new_max_i8;

            j = j + 1;
        }

        let final_count = (max_pos_concrete - min_pos_concrete + 1) as i8;
        results.push(final_count);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}