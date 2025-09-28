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
// <vc-helpers>
spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 {
        0
    } else if n > 0 {
        sum_negatives_to(a, n - 1) + if a@[n - 1] < 0 { a@[n - 1] as int } else { 0 }
    } else {
        0
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: int = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            sum == sum_negatives_to(a, i as int)
        decreases (a.len() as int - i as int)
    {
        if a[i] < 0 {
            sum = sum + (a[i] as int);
        }
        i += 1;
    }
    let result: i32 = sum as i32;
    assert(result as int == sum);
    result
}
// </vc-code>

fn main() {}

}