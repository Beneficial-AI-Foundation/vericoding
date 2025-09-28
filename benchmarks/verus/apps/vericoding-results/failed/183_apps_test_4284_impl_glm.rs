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
/* helper modified by LLM (iteration 5): use int arithmetic to avoid overflow */
fn compute_max_action_a_turns(k: i8, n: i8, a: i8, b: i8) -> (result: i8)
    requires valid_query(k as int, n as int, a as int, b as int),
    ensures
        result as int == max_action_a_turns(k as int, n as int, a as int, b as int),
        valid_result(result as int, k as int, n as int, a as int, b as int),
{
    let k_int = k as int;
    let n_int = n as int;
    let a_int = a as int;
    let b_int = b as int;

    if n_int * b_int > k_int {
        -1
    } else {
        let max_possible = (k_int - n_int * b_int - 1) / (a_int - b_int);
        if n_int <= max_possible {
            n
        } else {
            // max_possible is in [-1, 125] so it fits in i8
            max_possible as i8
        }
    }
}
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
{
    /* code modified by LLM (iteration 5): added assertion to prove query validity */
    let mut results = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> 
                results[j] as int == max_action_a_turns(#[trigger] queries[j].0 as int, queries[j].1 as int, queries[j].2 as int, queries[j].3 as int),
            forall|j: int| 0 <= j < i ==> 
                valid_result(#[trigger] results[j] as int, queries[j].0 as int, queries[j].1 as int, queries[j].2 as int, queries[j].3 as int),
        decreases queries.len() - i,
    {
        let (k, n, a, b) = queries[i];
        // Prove that the current query is valid to satisfy the helper's precondition
        assert(valid_query(k as int, n as int, a as int, b as int));
        let result = compute_max_action_a_turns(k, n, a, b);
        results.push(result);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}