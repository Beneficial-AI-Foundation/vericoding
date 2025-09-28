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
/* helper modified by LLM (iteration 3): lemma that max_action_a_turns satisfies valid_result */
fn prove_max_action_valid(k: int, n: int, a: int, b: int)
    requires
        valid_query(k, n, a, b),
    ensures
        valid_result(max_action_a_turns(k, n, a, b), k, n, a, b),
{
    let r = max_action_a_turns(k, n, a, b);
    if n * b > k {
        assert(r == -1);
        assert(valid_result(r, k, n, a, b));
    } else {
        let max_possible = (k - n * b - 1) / (a - b);
        if n <= max_possible {
            assert(r == n);
            assert(0 <= r && r <= n);
            assert(valid_result(r, k, n, a, b));
        } else {
            assert(r == max_possible);
            assert(0 <= r && r <= n);
            assert(valid_result(r, k, n, a, b));
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
/* code modified by LLM (iteration 3): compute runtime result and prove it matches spec */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: nat = 0;
    while i < queries.len()
        invariant
            results.len() as int == i as int,
            results.len() <= queries.len(),
        decreases queries.len() - i
    {
        let (k8, n8, a8, b8) = queries[i];
        let k_i64 = k8 as i64;
        let n_i64 = n8 as i64;
        let a_i64 = a8 as i64;
        let b_i64 = b8 as i64;
        let res_i64: i64;
        if n_i64 * b_i64 > k_i64 {
            res_i64 = -1;
        } else {
            let max_possible = (k_i64 - n_i64 * b_i64 - 1) / (a_i64 - b_i64);
            if n_i64 <= max_possible { res_i64 = n_i64; } else { res_i64 = max_possible; }
        }
        let res_i8 = res_i64 as i8;
        results.push(res_i8);
        proof {
            let k = k8 as int;
            let n = n8 as int;
            let a = a8 as int;
            let b = b8 as int;
            let res_int = res_i8 as int;
            if n * b > k {
                assert(res_int == -1);
                assert(max_action_a_turns(k, n, a, b) == -1);
            } else {
                let max_possible = (k - n * b - 1) / (a - b);
                if n <= max_possible {
                    assert(res_int == n);
                    assert(max_action_a_turns(k, n, a, b) == n);
                } else {
                    assert(res_int == max_possible);
                    assert(max_action_a_turns(k, n, a, b) == max_possible);
                }
            }
            assert(res_int == max_action_a_turns(k, n, a, b));
            prove_max_action_valid(k, n, a, b);
        }
        i = i + 1;
    }
    results
}

// </vc-code>


}

fn main() {}