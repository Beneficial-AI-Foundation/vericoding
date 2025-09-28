// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn collision_count(n: int) -> int
    recommends valid_input(n)
{
    n * n
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result == collision_count(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implemented accumulation loop to compute n*n using i32 for calculation, handling potential overflow in return cast */
  let mut c: i32 = 0;
  let mut i: i32 = 0;
  while i < (n as i32)
      invariant
          c as int >= 0,
          i as int >= 0,
          i as int <= n as int,
          c as int == i as int * n as int,
          valid_input(n as int)
      decreases n as int - i as int
  {
      c = c + (n as i32);
      i = i + 1;
  }
  proof {
      assert(i as int == n as int);
      assert(c as int == n as int * n as int);
  }
  (c as i8)
}
// </vc-code>


}

fn main() {}