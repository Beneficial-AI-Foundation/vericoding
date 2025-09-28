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
/* code modified by LLM (iteration 5): Corrected forall syntax in loop invariant by moving #[trigger] annotation after the variable binding to fix compilation error */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len() as int,
            results.len() as int == i as int,
            forall |j: int| #[trigger(queries@[j])] 0 <= j < i ==> {
                let qj = queries@[j];
                let kj = qj.0 as int;
                let nj = qj.1 as int;
                let aj = qj.2 as int;
                let bj = qj.3 as int;
                results@[j] as int == max_action_a_turns(kj, nj, aj, bj)
            }
        decreases queries.len() as int - i as int
    {
        let q = queries[i];
        let k: i64 = q.0 as i64;
        let n: i64 = q.1 as i64;
        let a: i64 = q.2 as i64;
        let b: i64 = q.3 as i64;
        let res: i64 = if n * b > k {
            -1
        } else {
            let diff: i64 = a - b;
            let numerator: i64 = k - n * b - 1;
            let max_p: i64 = numerator / diff;
            if n <= max_p {
                n
            } else {
                max_p
            }
        };
        proof {
            assert(res as int == max_action_a_turns(k as int, n as int, a as int, b as int));
        }
        results.push(res as i8);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}