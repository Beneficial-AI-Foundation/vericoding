// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: int) -> int
  decreases exp
{
  if exp <= 0 { 1 }
  else { base * pow(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
 
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (years: i8)
  requires 
      1 <= a <= b <= 10,
      forall|base: int, exp: int| exp >= 0 ==> (
          (exp == 0 ==> pow(base, exp) == 1) &&
          (exp > 0 && base > 0 ==> pow(base, exp) > 0) &&
          (exp > 0 && base == 0 ==> pow(base, exp) == 0)
      ),
  ensures 
      years >= 0,
      (a as int) * pow(3, years as int) > (b as int) * pow(2, years as int),
      years == 0 || (a as int) * pow(3, (years - 1) as int) <= (b as int) * pow(2, (years - 1) as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): switched to i128 types for power accumulators to avoid multiplication overflow in while condition */{
    let mut y: i8 = 0;
    let mut left_pow: i128 = 1;
    let mut right_pow: i128 = 1;
    proof {
        assert(left_pow as int == pow(3, y as int));
        assert(right_pow as int == pow(2, y as int));
    }
    while (a as i128) * left_pow <= (b as i128) * right_pow
        invariant
            y >= 0,
            left_pow as int == pow(3, y as int),
            right_pow as int == pow(2, y as int),
            forall |k: int| 0 <= k < y ==> (a as int) * pow(3, k) <= (b as int) * pow(2, k),
            y <= 11
        decreases 11 - y
    {
        proof {
            assert(forall |k: int| 0 <= k < y ==> (a as int) * pow(3, k) <= (b as int) * pow(2, k));
        }
        y = y + 1;
        left_pow = left_pow * 3;
        right_pow = right_pow * 2;
        proof {
            assert(left_pow as int == pow(3, y as int));
            assert(right_pow as int == pow(2, y as int));
        }
    }
    y
}
// </vc-code>


}

fn main() {}