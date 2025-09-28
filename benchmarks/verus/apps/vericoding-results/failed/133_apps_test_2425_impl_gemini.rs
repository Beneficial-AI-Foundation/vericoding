// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power2(k: nat) -> int
    decreases k
{
    if k == 0 { 1 } else { 2 * power2((k - 1) as nat) }
}

spec fn valid_query(a: int) -> bool
{
    2 <= a <= power2(25) - 1
}

spec fn valid_queries(queries: Seq<int>) -> bool
{
    forall|i: int| #![auto] 0 <= i < queries.len() ==> valid_query(queries[i])
}

spec fn largest_proper_divisor(n: int) -> int
    recommends n > 1
{
    if n <= 1 { 
        1 
    } else { 
        largest_proper_divisor_helper(n, 2) 
    }
}

spec fn largest_proper_divisor_helper(n: int, d: int) -> int
    recommends n > 1 && d >= 2
    decreases if n >= d { n - d } else { 0 }
{
    if d * d > n { 
        1 
    } else if n % d == 0 { 
        let quotient = n / d;
        if quotient == d { 
            quotient 
        } else if n > d {
            let remainder_check = largest_proper_divisor_helper(n, d + 1);
            if quotient > remainder_check { quotient } else { remainder_check }
        } else {
            quotient
        }
    } else if n > d { 
        largest_proper_divisor_helper(n, d + 1) 
    } else {
        1
    }
}

spec fn valid_results(queries: Seq<int>, results: Seq<int>) -> bool
{
    results.len() == queries.len() &&
    (forall|i: int| 0 <= i < results.len() ==> results[i] >= 1) &&
    true
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [changed parameters to i32 to fix compilation issue] */
fn compute_largest_proper_divisor_recursive(n: i32, d: i32) -> (result: i32)
    requires
        2 <= n <= 127,
        d >= 2,
    ensures
        result as int == largest_proper_divisor_helper(n as int, d as int),
        1 <= result <= 63,
    decreases n - d
{
    if d * d > n {
        1
    } else if n % d == 0 {
        let quotient = n / d;
        if quotient == d {
            quotient
        } else {
            let remainder_check = compute_largest_proper_divisor_recursive(n, d + 1);
            if quotient > remainder_check {
                quotient
            } else {
                remainder_check
            }
        }
    } else {
        compute_largest_proper_divisor_recursive(n, d + 1)
    }
}

/* helper modified by LLM (iteration 3): [fixed compilation error by using i32 instead of ghost int] */
fn compute_largest_proper_divisor(query: i8) -> (result: i8)
    requires
        valid_query(query as int),
    ensures
        result as int == largest_proper_divisor(query as int),
{
    let n = query as i32;
    let lpd = compute_largest_proper_divisor_recursive(n, 2);
    lpd as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_queries(queries@.map(|_i, x: i8| x as int))
    ensures valid_results(queries@.map(|_i, x: i8| x as int), results@.map(|_i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [logic unchanged; fix was in a helper function] */
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            queries@.len() == old(queries)@.len(),
            valid_queries(queries@.map(|_i, x: i8| x as int)),
            results@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                results@[j] as int == largest_proper_divisor(queries@[j] as int),

    {
        let query = queries[i];
        let result = compute_largest_proper_divisor(query);
        results.push(result);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}