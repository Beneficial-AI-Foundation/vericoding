// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn digit_sum(n: int) -> int
  decreases n when n >= 0
{
  if n <= 0 { 
    0 
  } else { 
    (n % 10) + digit_sum(n / 10) 
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keep spec function for digit sum computation */
spec fn compute_digit_sum(n: i8) -> int
    requires n >= 0
    ensures compute_digit_sum(n) == digit_sum(n as int)
    decreases n
{
    if n <= 0 {
        0
    } else {
        (n % 10) as int + compute_digit_sum((n / 10) as i8)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    n >= 1,
  ensures 
    n == 1 ==> result == -1,
    n > 1 && result > 0 ==> (result as int) * (result as int) + digit_sum(result as int) * (result as int) == n as int,
    n > 1 && result > 0 ==> forall|y: int| y > 0 && y < result as int ==> y * y + digit_sum(y) * y != n as int,
    n > 1 && result == -1 ==> forall|x: int| x > 0 ==> x * x + digit_sum(x) * x != n as int,
    result == -1 || result > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int usage - compute in ghost code then use result */
    if n == 1 {
        return -1;
    }
    
    let mut x: i8 = 1;
    
    while x <= 127
        invariant
            x >= 1,
            forall|y: int| 1 <= y && y < x as int ==> y * y + digit_sum(y) * y != n as int,
    {
        // Check for overflow before multiplication
        if x > 11 {  // x^2 > 121 would overflow i8
            return -1;
        }
        
        let x_squared = x * x;
        
        // Compute digit sum in ghost code
        let ghost ds = compute_digit_sum(x);
        
        // Check if ds * x would overflow and compute it if safe
        let ds_times_x: i8;
        proof {
            if ds > 127 / (x as int) {
                ds_times_x = 127;  // Will trigger overflow check below
            } else {
                assert(ds * (x as int) <= 127);
                assert(ds * (x as int) >= -128);
                ds_times_x = (ds * (x as int)) as i8;
            }
        }
        
        // Check for overflow before addition
        if x_squared > 127 - ds_times_x {
            return -1;
        }
        
        let product = x_squared + ds_times_x;
        
        proof {
            assert(product as int == (x as int) * (x as int) + digit_sum(x as int) * (x as int));
        }
        
        if product == n {
            return x;
        }
        
        if product > n {
            return -1;
        }
        
        x = x + 1;
    }
    
    -1
}
// </vc-code>


}

fn main() {}