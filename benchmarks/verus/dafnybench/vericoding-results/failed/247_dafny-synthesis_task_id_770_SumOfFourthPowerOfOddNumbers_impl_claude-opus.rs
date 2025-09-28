use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove the recurrence relation for the sum
proof fn sum_fourth_power_recurrence(k: i32)
    requires 
        0 <= k,
        k < i32::MAX / 2 - 1,
    ensures 
        k as int * (2 * k as int + 1) * (24 * (k as int) * (k as int) * (k as int) - 12 * (k as int) * (k as int) - 14 * k as int + 7) / 15
        + (2 * k as int + 1) * (2 * k as int + 1) * (2 * k as int + 1) * (2 * k as int + 1)
        == (k + 1) as int * (2 * (k + 1) as int + 1) * (24 * ((k + 1) as int) * ((k + 1) as int) * ((k + 1) as int) - 12 * ((k + 1) as int) * ((k + 1) as int) - 14 * (k + 1) as int + 7) / 15
{
    let k_int = k as int;
    
    // Left side calculation
    let left_sum = k_int * (2 * k_int + 1) * (24 * k_int * k_int * k_int - 12 * k_int * k_int - 14 * k_int + 7) / 15;
    let odd_fourth = (2 * k_int + 1) * (2 * k_int + 1) * (2 * k_int + 1) * (2 * k_int + 1);
    
    // Right side calculation  
    let k1 = k_int + 1;
    let right_sum = k1 * (2 * k1 + 1) * (24 * k1 * k1 * k1 - 12 * k1 * k1 - 14 * k1 + 7) / 15;
    
    // Expand the fourth power of (2k+1)
    assert(odd_fourth == 16 * k_int * k_int * k_int * k_int + 32 * k_int * k_int * k_int + 24 * k_int * k_int + 8 * k_int + 1);
    
    // Expand right side expression
    assert(2 * k1 + 1 == 2 * k_int + 3);
    assert(24 * k1 * k1 * k1 - 12 * k1 * k1 - 14 * k1 + 7 
           == 24 * (k_int + 1) * (k_int + 1) * (k_int + 1) - 12 * (k_int + 1) * (k_int + 1) - 14 * (k_int + 1) + 7);
    
    // Expand the cubic term
    assert((k_int + 1) * (k_int + 1) * (k_int + 1) == k_int * k_int * k_int + 3 * k_int * k_int + 3 * k_int + 1);
    
    // Expand the quadratic term
    assert((k_int + 1) * (k_int + 1) == k_int * k_int + 2 * k_int + 1);
    
    // Now expand the full expression for the right side
    assert(24 * k1 * k1 * k1 - 12 * k1 * k1 - 14 * k1 + 7
           == 24 * (k_int * k_int * k_int + 3 * k_int * k_int + 3 * k_int + 1) 
              - 12 * (k_int * k_int + 2 * k_int + 1) 
              - 14 * (k_int + 1) + 7);
    
    assert(24 * k1 * k1 * k1 - 12 * k1 * k1 - 14 * k1 + 7
           == 24 * k_int * k_int * k_int + 72 * k_int * k_int + 72 * k_int + 24
              - 12 * k_int * k_int - 24 * k_int - 12
              - 14 * k_int - 14 + 7);
              
    assert(24 * k1 * k1 * k1 - 12 * k1 * k1 - 14 * k1 + 7
           == 24 * k_int * k_int * k_int + 60 * k_int * k_int + 34 * k_int + 5);
    
    // The full right side
    assert(right_sum == (k_int + 1) * (2 * k_int + 3) * (24 * k_int * k_int * k_int + 60 * k_int * k_int + 34 * k_int + 5) / 15);
    
    // Multiply out (k_int + 1) * (2 * k_int + 3)
    assert((k_int + 1) * (2 * k_int + 3) == 2 * k_int * k_int + 5 * k_int + 3);
    
    // The identity holds by algebraic calculation
    assert(left_sum + odd_fourth == right_sum);
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            i <= i32::MAX / 2 - 1,
            n <= i32::MAX / 2 - 1,
            sum == if i == 0 { 0 } else { (i as int * (2 * i as int + 1) * (24 * (i as int) * (i as int) * (i as int) - 12 * (i as int) * (i as int) - 14 * i as int + 7) / 15) as i32 },
        decreases n - i,
    {
        let odd = 2 * i + 1;
        let odd_squared = odd * odd;
        let odd_fourth = odd_squared * odd_squared;
        
        if i == 0 {
            assert(odd == 1);
            assert(odd_fourth == 1);
            assert(1 == (1 as int * 3 * (24 - 12 - 14 + 7) / 15) as i32);
            assert(1 == (1 as int * 3 * 5 / 15) as i32);
            assert(1 == (15 / 15) as i32);
            assert(1 == 1);
            sum = odd_fourth;
        } else {
            proof {
                sum_fourth_power_recurrence(i);
                assert(sum as int == i as int * (2 * i as int + 1) * (24 * (i as int) * (i as int) * (i as int) - 12 * (i as int) * (i as int) - 14 * i as int + 7) / 15);
                assert(odd_fourth as int == (2 * i as int + 1) * (2 * i as int + 1) * (2 * i as int + 1) * (2 * i as int + 1));
                assert(sum as int + odd_fourth as int == 
                       ((i + 1) as int * (2 * (i + 1) as int + 1) * 
                        (24 * ((i + 1) as int) * ((i + 1) as int) * ((i + 1) as int) - 
                         12 * ((i + 1) as int) * ((i + 1) as int) - 
                         14 * (i + 1) as int + 7) / 15));
            }
            sum = sum + odd_fourth;
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {}

}