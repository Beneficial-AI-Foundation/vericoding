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
/* helper modified by LLM (iteration 3): fixed division type error */
fn digit_sum_i8(x: i8) -> i8 {
    let mut n = x;
    let mut sum = 0;
    while n != 0 {
        sum += n % 10;
        n = (n / 10) as i8;
    }
    sum
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
/* code modified by LLM (iteration 3): fixed type errors in proof block */
{
    if n == 1 {
        return -1;
    }
    let mut x: i8 = 1;
    while x <= 11
        invariant 
            1 <= x as int <= 12,
            forall|y: int| 1 <= y < x as int ==> y * (y + digit_sum(y)) != n as int,
        decreases 12 - (x as int)
    {
        let ds = digit_sum_i8(x);
        let product = (x as i16) * (x as i16 + ds as i16);
        if product == n as i16 {
            proof {
                let mut n_val = x;
                let mut ghost_n_val = x as int;
                let mut sum_non_ghost: int = 0;
                let mut sum_ghost = 0;

                while n_val != 0
                    invariant
                        n_val == ghost_n_val as i8,
                        sum_non_ghost == sum_ghost,
                        sum_non_ghost + (digit_sum_i8(n_val) as int) == (digit_sum_i8(x) as int),
                        sum_ghost + digit_sum(ghost_n_val) == digit_sum(x as int),
                {
                    let last_digit_non_ghost = n_val % 10;
                    n_val = (n_val / 10) as i8;
                    sum_non_ghost += last_digit_non_ghost as int;

                    let last_digit_ghost = ghost_n_val % 10;
                    ghost_n_val = ghost_n_val / 10;
                    sum_ghost += last_digit_ghost;

                    assert(last_digit_non_ghost as int == last_digit_ghost);
                }
            }
            return x;
        }
        x += 1;
    }
    return -1;
}
// </vc-code>


}

fn main() {}