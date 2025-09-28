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
/* helper modified by LLM (iteration 5): runtime digit sum using i64 for executable code */
fn digit_sum_exec(mut m: i64) -> i64
    requires
        m >= 0,
    ensures
        result >= 0,
{
    let mut s: i64 = 0;
    while m > 0
        invariant
            m >= 0,
        decreases
            m,
    {
        let d = m % 10;
        s = s + d;
        m = m / 10;
    }
    s
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
  /* code modified by LLM (iteration 5): search for smallest x and compute digit sum with inner loop invariant relating to spec digit_sum */
  if n == 1 {
    return -1;
  }
  let ni: i64 = n as i64;
  let mut x: i64 = 1;
  while x <= ni
      invariant
          x >= 1,
      decreases
          ni - x + 1,
  {
      // compute digit sum of x with an inner loop that maintains relation to spec digit_sum
      let mut t: i64 = x;
      let mut ds: i64 = 0;
      while t > 0
          invariant
              t >= 0,
              ds as int + digit_sum(t as int) == digit_sum(x as int),
          decreases
              t,
      {
          let d = t % 10;
          ds = ds + d;
          t = t / 10;
      }
      let val: i64 = x * x + ds * x;
      if val == ni {
          return x as i8;
      }
      x = x + 1;
  }
  -1
}
// </vc-code>


}

fn main() {}