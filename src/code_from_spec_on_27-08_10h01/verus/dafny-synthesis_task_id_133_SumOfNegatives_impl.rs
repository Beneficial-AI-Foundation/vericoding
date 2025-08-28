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
proof fn sum_negatives_to_step(a: &[i32], n: int)
    requires 0 <= n < a.len()
    ensures 
        if a[n] < 0 {
            sum_negatives_to(a, n + 1) == sum_negatives_to(a, n) + a[n]
        } else {
            sum_negatives_to(a, n + 1) == sum_negatives_to(a, n)
        }
{
    // Proof follows from definition
}

spec fn abs_spec(x: i32) -> int {
    if x >= 0 { x as int } else { -(x as int) }
}

proof fn sum_bounds_lemma(a: &[i32], i: usize)
    requires 
        0 <= i < a.len(),
        a[i] < 0,
        abs_spec(sum_negatives_to(a, i as int)) <= (i as int) * (i32::MAX as int / 2),
        abs_spec(a[i] as int) <= i32::MAX as int / 2
    ensures abs_spec(sum_negatives_to(a, i as int) + a[i] as int) <= ((i + 1) as int) * (i32::MAX as int / 2)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sum == sum_negatives_to(a, i as int),
            abs_spec(sum) <= (i as int) * (i32::MAX as int / 2)
        decreases a.len() - i
    {
        if a[i] < 0 {
            proof {
                sum_negatives_to_step(a, i as int);
                sum_bounds_lemma(a, i);
            }
            sum = sum.wrapping_add(a[i]);
        } else {
            proof {
                sum_negatives_to_step(a, i as int);
            }
        }
        i += 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}