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
proof fn sum_negatives_to_bounds(a: &[i32], n: int)
    requires 
        0 <= n <= a.len(),
    ensures 
        sum_negatives_to(a, n) <= 0,
        sum_negatives_to(a, n) >= n * (i32::MIN as int),
    decreases n,
{
    if n == 0 {
        assert(sum_negatives_to(a, n) == 0);
    } else if n > 0 && a[n - 1] < 0 {
        sum_negatives_to_bounds(a, (n - 1) as int);
        assert(a[n - 1] >= i32::MIN);
        assert(sum_negatives_to(a, n) == sum_negatives_to(a, n - 1) + a[n - 1]);
        assert(sum_negatives_to(a, n - 1) >= (n - 1) * (i32::MIN as int));
        assert(sum_negatives_to(a, n) >= (n - 1) * (i32::MIN as int) + i32::MIN);
        assert((n - 1) * (i32::MIN as int) + i32::MIN == n * (i32::MIN as int));
    } else if n > 0 {
        sum_negatives_to_bounds(a, (n - 1) as int);
        assert(sum_negatives_to(a, n) == sum_negatives_to(a, n - 1));
        assert(sum_negatives_to(a, n - 1) >= (n - 1) * (i32::MIN as int));
        assert(sum_negatives_to(a, n) >= (n - 1) * (i32::MIN as int));
        assert((n - 1) * (i32::MIN as int) >= n * (i32::MIN as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sum == sum_negatives_to(a, i as int),
            sum <= 0,
            sum >= i * (i32::MIN as int),
        decreases a.len() - i,
    {
        proof {
            sum_negatives_to_bounds(a, (i + 1) as int);
        }
        
        if a[i] < 0 {
            assert(sum_negatives_to(a, (i + 1) as int) == sum_negatives_to(a, i as int) + a[i as int]);
            sum = sum + a[i];
        } else {
            assert(sum_negatives_to(a, (i + 1) as int) == sum_negatives_to(a, i as int));
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}