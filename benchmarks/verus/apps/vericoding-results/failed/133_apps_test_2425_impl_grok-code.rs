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
/* helper modified by LLM (iteration 5): removed illegal use of 'int' type in executable code by performing i64 arithmetic directly */
fn compute_largest_divisor(n: i64) -> (r: i64)
    requires
        2 <= n as int,
        n as int < power2(26), // to avoid overflow
    ensures
        r as int == largest_proper_divisor(n as int),
{
    let mut current_max = 1i64;
    let mut d = 2i64;
    while d * d <= n
        invariant
            2 <= d as int,
            d as int <= n as int + 1,
            1 <= current_max as int,
            current_max as int <= n as int,
        decreases (n as int - d as int)
    {
        if n % d == 0 {
            let q = n / d;
            let max_pair = if d < q { q } else { d };
            current_max = if current_max < max_pair { max_pair } else { current_max };
        }
        d = d + 1;
    }
    current_max
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_queries(queries@.map(|_i, x: i8| x as int))
    ensures valid_results(queries@.map(|_i, x: i8| x as int), results@.map(|_i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant syntax error by correcting forall quantifier */
{
    let mut results = Vec::new();
    let mut ii = 0;
    while ii < queries.len()
        invariant
            0 <= ii <= queries.len(),
            valid_queries(queries@.map(|_j, x: i8| x as int)),
            results@.len() == ii as int,
            forall|k: int| 0 <= k < ii ==> results@[k] as int == largest_proper_divisor(queries@.map(|_j, x: i8| x as int)[k]),
        decreases queries.len() - ii
    {
        let query = queries[ii];
        proof {
            assert(valid_queries(queries@.map(|_j, x: i8| x as int)));
            assert(2 <= query as int);
        }
        let res = compute_largest_divisor(query as i64);
        results.push(#[verifier::truncate] (res as i8));
        ii = ii + 1;
    }
    results
}
// </vc-code>


}

fn main() {}