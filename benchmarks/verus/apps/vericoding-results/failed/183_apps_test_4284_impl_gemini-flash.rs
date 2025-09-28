// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_query(k: int, n: int, a: int, b: int) -> bool {
    k > 0 && n > 0 && a > 0 && b > 0 && b < a
}

spec fn max_action_a_turns(k: int, n: int, a: int, b: int) -> int {
    if n * b > k { 
        -1
    } else { 
        let max_possible = (k - n * b - 1) / (a - b);
        if n <= max_possible { n } else { max_possible }
    }
}

spec fn valid_result(result: int, k: int, n: int, a: int, b: int) -> bool {
    result == -1 || (0 <= result <= n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper (original was empty) */
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(i8, i8, i8, i8)>) -> (results: Vec<i8>)
    requires 
        queries.len() > 0,
        forall|i: int| 0 <= i < queries.len() ==> valid_query(#[trigger] queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
    ensures 
        results.len() == queries.len(),
        forall|i: int| 0 <= i < queries.len() ==> results[i as int] as int == max_action_a_turns(#[trigger] queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
        forall|i: int| 0 <= i < results.len() ==> valid_result(#[trigger] results[i as int] as int, queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `int` to `i8` type cast when `max_possible_a_turns_int` is written to result. Added `proof` block to show arithmetic properties for verification. */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < queries.len()
        invariant 
            0 <= (i as int) && (i as int) <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j as int] as int == max_action_a_turns(queries[j as int].0 as int, queries[j as int].1 as int, queries[j as int].2 as int, queries[j as int].3 as int),
            forall|k_inv: int| 0 <= k_inv < i ==> valid_result(results[k_inv as int] as int, queries[k_inv as int].0 as int, queries[k_inv as int].1 as int, queries[k_inv as int].2 as int, queries[k_inv as int].3 as int),
        decreases queries.len() - i
    {
        let query = queries[i]; // Accessing with i of type usize for concrete operation
        let k_i: i8 = query.0;
        let n_i: i8 = query.1;
        let a_i: i8 = query.2;
        let b_i: i8 = query.3;

        let k_ghost: int = k_i as int;
        let n_ghost: int = n_i as int;
        let a_ghost: int = a_i as int;
        let b_ghost: int = b_i as int;

        let result: i8;
        if n_ghost * b_ghost > k_ghost {
            result = -1;
        } else {
            let diff_ab: int = a_ghost - b_ghost;
            let max_possible_k_diff: int = k_ghost - n_ghost * b_ghost;
            let max_possible_a_turns_int: int = (max_possible_k_diff - 1) / diff_ab;

            proof {
                assert(valid_query(k_ghost, n_ghost, a_ghost, b_ghost));

                if diff_ab > 0 {
                    assert((max_possible_k_diff - 1) / diff_ab == (k_ghost - n_ghost * b_ghost - 1) / (a_ghost - b_ghost));
                }
            }

            if n_ghost <= max_possible_a_turns_int {
                result = n_i;
            } else {
                result = max_possible_a_turns_int as i8;
            }
        }
        results.push(result);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}