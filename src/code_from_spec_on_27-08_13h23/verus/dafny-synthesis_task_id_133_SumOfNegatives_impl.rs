use vstd::prelude::*;

verus! {

spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 { 
        0 
    } else if n > 0 && a[n - 1] < 0 { 
        sum_negatives_to(a, n - 1) + a[n - 1] 
    } else if n > 0 { 
        sum_negatives_to(a, n - 1) 
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_negatives_to(a: &[i32], n: int)
    requires 0 <= n <= a.len()
    ensures sum_negatives_to(a, n) == if n == 0 {
        0
    } else if n > 0 && a[n - 1] < 0 {
        sum_negatives_to(a, n - 1) + a[n - 1]
    } else {
        sum_negatives_to(a, n - 1)
    }
    decreases n
{
    if n == 0 {
    } else if n > 0 && a[n - 1] < 0 {
        lemma_sum_negatives_to(a, n - 1);
    } else {
        lemma_sum_negatives_to(a, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sum == sum_negatives_to(a, i as int)
    {
        if a[i] < 0 {
            sum = sum + a[i];
        }
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}