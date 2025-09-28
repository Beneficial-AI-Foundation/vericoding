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
/* helper modified by LLM (iteration 5): added bounds checking for multiplication and subtraction */
fn solve_helper(queries: Vec<(i8, i8, i8, i8)>, i: usize) -> (results: Vec<i8>)
    requires
        i <= queries.len(),
        forall|j: int| 0 <= j < queries.len() ==> valid_query(queries[j].0 as int, queries[j].1 as int, queries[j].2 as int, queries[j].3 as int),
    ensures
        results.len() == queries.len() - i,
        forall|j: int| 0 <= j < results.len() ==> results[j] as int == max_action_a_turns(queries[(i + j) as int].0 as int, queries[(i + j) as int].1 as int, queries[(i + j) as int].2 as int, queries[(i + j) as int].3 as int),
    decreases queries.len() - i,
{
    if i >= queries.len() {
        Vec::new()
    } else {
        let (k, n, a, b) = queries[i];
        let k64 = k as i64;
        let n64 = n as i64;
        let a64 = a as i64;
        let b64 = b as i64;
        
        proof {
            assert(k as int > 0 && n as int > 0 && a as int > 0 && b as int > 0 && (b as int) < (a as int));
            assert(n64 > 0 && b64 > 0 && k64 > 0);
            assert(a64 > b64 && a64 > 0);
            assert(n64 <= 127 && b64 <= 127);
            assert(n64 * b64 <= 127 * 127);
        }
        
        let product = n64 * b64;
        let result = if product > k64 {
            -1i8
        } else {
            let numerator = k64 - product - 1;
            let denominator = a64 - b64;
            let max_possible = numerator / denominator;
            if n64 <= max_possible {
                n
            } else {
                #[verifier::truncate] (max_possible as i8)
            }
        };
        let mut rest = solve_helper(queries, i + 1);
        let mut results = Vec::new();
        results.push(result);
        results.append(&mut rest);
        results
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
    /* code modified by LLM (iteration 5): added bounds checking for multiplication and subtraction */
    let mut results = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j] as int == max_action_a_turns(queries[j].0 as int, queries[j].1 as int, queries[j].2 as int, queries[j].3 as int),
            forall|j: int| 0 <= j < i ==> valid_result(results[j] as int, queries[j].0 as int, queries[j].1 as int, queries[j].2 as int, queries[j].3 as int),
        decreases queries.len() - i,
    {
        let (k, n, a, b) = queries[i];
        let k64 = k as i64;
        let n64 = n as i64;
        let a64 = a as i64;
        let b64 = b as i64;
        
        proof {
            assert(valid_query(queries[i].0 as int, queries[i].1 as int, queries[i].2 as int, queries[i].3 as int));
            assert(k as int > 0 && n as int > 0 && a as int > 0 && b as int > 0 && (b as int) < (a as int));
            assert(n64 > 0 && b64 > 0 && k64 > 0);
            assert(a64 > b64 && a64 > 0);
            assert(n64 <= 127 && b64 <= 127);
            assert(n64 * b64 <= 127 * 127);
        }
        
        let product = n64 * b64;
        let result = if product > k64 {
            -1i8
        } else {
            let numerator = k64 - product - 1;
            let denominator = a64 - b64;
            let max_possible = numerator / denominator;
            if n64 <= max_possible {
                n
            } else {
                #[verifier::truncate] (max_possible as i8)
            }
        };
        
        results.push(result);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}