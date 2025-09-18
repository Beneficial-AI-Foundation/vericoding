// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>

proof fn sum_to_lemma(a: &Vec<i32>, n: nat)
    requires
        n <= a.len(),
    ensures
        sum_to(a, n) == if n == 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] },
    decreases n
{
    if n > 0 {
        sum_to_lemma(a, n - 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut sum: i32 = a[0];
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == sum_to(a, i as int),
    {
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}