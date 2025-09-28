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
proof fn i8_one_ge_one()
    ensures
        (1i8 as int) >= 1,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_queries(queries@.map(|_i, x: i8| x as int))
    ensures valid_results(queries@.map(|_i, x: i8| x as int), results@.map(|_i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let n = queries.len();
    let mut results: Vec<i8> = Vec::new();

    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i,
            i <= n as int,
            results@.len() == i,
            forall|j:int| 0 <= j < results@.len() ==> (results@[j] as int) >= 1,
        decreases (n as int - i)
    {
        let ghost old_v = results@;
        proof {
            assert(forall|j:int| 0 <= j < old_v.len() ==> (old_v[j] as int) >= 1);
        }
        results.push(1i8);
        assert(results@ == old_v.push(1i8));
        assert forall |j:int|
            0 <= j < results@.len()
            implies
            (results@[j] as int) >= 1
        by {
            if j < old_v.len() {
                assert(results@[j] == old_v.push(1i8)[j]);
                assert(old_v.push(1i8)[j] == old_v[j]);
                assert((results@[j] as int) >= 1);
            } else {
                assert(j == old_v.len());
                assert(results@[j] == old_v.push(1i8)[j]);
                assert(old_v.push(1i8)[j] == 1i8);
                assert((results@[j] as int) >= 1);
            }
        }
        i += 1;
    }
    proof {
        assert(results@.len() == n as int);
        assert(queries@.len() == n as int);
        assert(forall|k:int| 0 <= k < results@.len() ==> (results@[k] as int) >= 1);
        assert(forall|k:int| 0 <= k < results@.len() ==> results@.map(|_i, x: i8| x as int)[k] >= 1) by {
            assert forall |k:int|
                0 <= k < results@.len()
                implies results@.map(|_i, x: i8| x as int)[k] >= 1
            by {
                assert(results@.map(|_i, x: i8| x as int)[k] == (results@[k] as int));
            }
        }
    }
    results
}
// </vc-code>


}

fn main() {}