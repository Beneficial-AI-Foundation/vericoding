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
proof fn digit_sum_nonneg(n: int)
    requires n >= 0,
    ensures digit_sum(n) >= 0,
    decreases n
{
    if n <= 0 {
    } else {
        digit_sum_nonneg(n / 10);
    }
}

proof fn digit_sum_monotonic(a: int, b: int)
    requires a >= 0, b >= 0, a <= b,
    ensures digit_sum(a) <= digit_sum(b),
    decreases b
{
    if b <= 0 {
    } else if a <= 0 {
        digit_sum_nonneg(b);
    } else {
        digit_sum_monotonic(a / 10, b / 10);
    }
}

spec fn compute_val(x: int) -> int {
    x * x + digit_sum(x) * x
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
    /* code modified by LLM (iteration 5): moved digit_sum computation to ghost code */
    if n == 1 {
        return -1i8;
    }
    
    let mut x = 1i8;
    while x < 127
        invariant
            1 <= x <= 127,
            n > 1,
            forall|y: int| 1 <= y < x ==> y * y + digit_sum(y) * y != n as int,
    {
        let x_int = x as int;
        let n_int = n as int;
        
        ghost let ghost_digit_sum = digit_sum(x_int);
        ghost let val = x_int * x_int + ghost_digit_sum * x_int;
        
        // Convert to executable computation
        let x_u64 = x as u64;
        let n_u64 = n as u64;
        
        // Compute digit sum in executable code
        let mut temp_x = x;
        let mut sum = 0u64;
        while temp_x > 0 {
            sum = sum + (temp_x % 10) as u64;
            temp_x = temp_x / 10;
        }
        
        let val_u64 = x_u64 * x_u64 + sum * x_u64;
        
        if val_u64 == n_u64 {
            proof {
                assert(val == n_int);
            }
            return x;
        }
        
        if val_u64 > n_u64 {
            return -1i8;
        }
        
        if x == 126 {
            break;
        }
        
        x = x + 1;
    }
    
    -1i8
}
// </vc-code>


}

fn main() {}