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
/* helper modified by LLM (iteration 5): added trigger annotation to quantifier in invariant */
fn compute_largest_proper_divisor(n: i32) -> (result: i32)
    requires 2 <= n
    ensures 
        1 <= result < n,
        n % result == 0,
        forall|d: i32| #![trigger n % d] 1 <= d < n && n % d == 0 ==> d <= result
{
    let mut i: i32 = 2;
    let mut divisor: i32 = 1;
    while i * i <= n
        invariant 
            2 <= i,
            divisor == 1 ==> (forall|j: i32| #![trigger n % j] 2 <= j < i ==> n % j != 0),
            divisor != 1 ==> (exists|k: i32| 2 <= k <= i && divisor == n / k && n % k == 0)
        decreases (n - i)
    {
        if n % i == 0 {
            divisor = n / i;
            break;
        }
        i = i + 1;
    }
    divisor
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_queries(queries@.map(|_i, x: i8| x as int))
    ensures valid_results(queries@.map(|_i, x: i8| x as int), results@.map(|_i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): updated iteration number in comment */
    let mut results = Vec::new();
    for query in queries {
        let n = query as i32;
        let res = compute_largest_proper_divisor(n);
        results.push(res as i8);
    }
    results
}
// </vc-code>


}

fn main() {}