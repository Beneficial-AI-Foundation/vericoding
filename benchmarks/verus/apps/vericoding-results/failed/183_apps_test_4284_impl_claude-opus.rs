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
    /* code modified by LLM (iteration 5): Fixed compilation errors by moving int conversions into proof block */
    let mut results = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j as int] as int == max_action_a_turns(queries[j as int].0 as int, queries[j as int].1 as int, queries[j as int].2 as int, queries[j as int].3 as int),
            forall|j: int| 0 <= j < i ==> valid_result(results[j as int] as int, queries[j as int].0 as int, queries[j as int].1 as int, queries[j as int].2 as int, queries[j as int].3 as int),
        decreases queries.len() - i
    {
        let (k, n, a, b) = queries[i];
        
        // Compute result directly with i8 arithmetic
        let result = if (n as i32) * (b as i32) > (k as i32) {
            -1i8
        } else {
            let max_possible = ((k as i32) - (n as i32) * (b as i32) - 1) / ((a as i32) - (b as i32));
            if (n as i32) <= max_possible {
                n
            } else if max_possible >= 0 && max_possible <= 127 {
                max_possible as i8
            } else if max_possible < 0 {
                0i8
            } else {
                127i8
            }
        };
        
        proof {
            // Verify that our computed result matches the spec
            let k_int = k as int;
            let n_int = n as int;
            let a_int = a as int;
            let b_int = b as int;
            let spec_result = max_action_a_turns(k_int, n_int, a_int, b_int);
            assert(result as int == spec_result);
        }
        
        results.push(result);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}