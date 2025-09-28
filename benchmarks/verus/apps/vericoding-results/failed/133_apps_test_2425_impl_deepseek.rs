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
/* helper modified by LLM (iteration 5): add casting helper function */
fn largest_proper_divisor_exec(n: i8) -> i8
    requires n > 1
    ensures result == largest_proper_divisor(n as int) as i8
{
    let mut d: i8 = 2;
    let mut max_divisor: i8 = 1;
    
    while d * d <= n
        invariant
            d >= 2 && d <= n + 1,
            max_divisor >= 1,
            max_divisor <= largest_proper_divisor(n as int) as i8
        decreases (n - d) as int
    {
        if n % d == 0 {
            let quotient = n / d;
            if quotient > max_divisor {
                max_divisor = quotient;
            }
        }
        d += 1;
    }
    max_divisor
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_queries(queries@.map(|_i, x: i8| x as int))
    ensures valid_results(queries@.map(|_i, x: i8| x as int), results@.map(|_i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use execution function instead of ghost function */
{
    let mut results = Vec::new();
    let len = queries.len();
    let mut i = 0;
    while i < len
        invariant
            i >= 0 && i <= len,
            results.len() == i,
            valid_results(queries@.map(|j, x: i8| x as int).subrange(0, i as int), results@.map(|j, x: i8| x as int))
        decreases len - i
    {
        let query = queries.index(i);
        let result = largest_proper_divisor_exec(query);
        results.push(result);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}