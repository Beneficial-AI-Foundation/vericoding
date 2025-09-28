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
proof fn lemma_digit_sum_non_negative(n: int)
    requires
        n >= 0,
    ensures
        digit_sum(n) >= 0,
{
    // Proof by induction
    if n > 0 {
        lemma_digit_sum_non_negative(n / 10);
    }
}

proof fn lemma_digit_sum_bounded(n: int)
    requires
        n >= 0,
    ensures
        digit_sum(n) <= 9 * (1 + (n as nat).log10() as int),
{
    if n > 0 {
        lemma_digit_sum_bounded(n / 10);
    }
}

spec fn upper_bound(n: i8) -> i8 {
    n
}

/* helper modified by LLM (iteration 5): Fixed digit_sum spec function for exec context */
spec fn digit_sum_exec(x: int) -> i32
    decreases x when x >= 0
{
    if x <= 0 {
        0
    } else {
        ((x % 10) + digit_sum_exec(x / 10)) as i32
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
    /* code modified by LLM (iteration 5): Fixed digit_sum call using ghost function */
    if n == 1 {
        return -1;
    }
    
    let upper: i8 = upper_bound(n);
    let mut x: i8 = 1;
    
    while x <= upper
        invariant
            x >= 0,
            x <= upper + 1,
            forall|y: int| y > 0 && y < x as int ==> y * y + digit_sum(y) * y != n as int,
        decreases (upper as int) - (x as int)
    {
        let x_i = x;
        proof {
            lemma_digit_sum_non_negative(x_i as int);
        }
        let ds_val = digit_sum_exec(x_i as int);
        let total: i32 = (x_i as i32) * (x_i as i32) + ds_val * (x_i as i32);
        
        if total == n as i32 {
            return x;
        }
        
        x = x + 1;
    }
    
    return -1;
}
// </vc-code>


}

fn main() {}