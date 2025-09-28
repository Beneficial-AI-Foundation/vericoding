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
proof fn sum_negatives_to_monotonic(a: &[i32], n1: int, n2: int)
    requires 0 <= n1 <= n2 <= a.len()
    ensures sum_negatives_to(a, n1) <= sum_negatives_to(a, n2) || sum_negatives_to(a, n1) >= sum_negatives_to(a, n2)
    decreases n2
{
    if n1 == n2 {
    } else if n2 > 0 {
        sum_negatives_to_monotonic(a, n1, n2 - 1);
    }
}

proof fn sum_negatives_to_bounds(a: &[i32], n: int)
    requires 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] >= -1000000000,
    ensures sum_negatives_to(a, n) >= -1000000000 * n
    decreases n
{
    if n == 0 {
    } else if n > 0 {
        sum_negatives_to_bounds(a, n - 1);
        if a[n - 1] < 0 {
            assert(a[n - 1] >= -1000000000);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result == sum_negatives_to(a, i as int)
    {
        if a[i as int] < 0 {
            result = result + a[i as int];
        }
        
        assert(sum_negatives_to(a, (i + 1) as int) == 
               if a[i as int] < 0 { 
                   sum_negatives_to(a, i as int) + a[i as int] 
               } else { 
                   sum_negatives_to(a, i as int) 
               });
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}