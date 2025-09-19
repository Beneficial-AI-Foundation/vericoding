// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
  a >= 1 && b >= a && c >= 1 && d >= 1
}

spec fn not_divisible_by_either(x: int, c: int, d: int) -> bool
  recommends c > 0 && d > 0
{
  x % c != 0 && x % d != 0
}

spec fn count_not_divisible(a: int, b: int, c: int, d: int) -> int
  recommends valid_input(a, b, c, d)
{
  /* Count of integers in range [a, b] not divisible by either c or d */
  (Set::new(|x: int| a <= x <= b && not_divisible_by_either(x, c, d))).len() as int
}
spec fn f(n: int, c: int, d: int) -> int {
  /* Helper function f referenced in postcondition */
  0 as int  /* Placeholder specification */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
  requires
      valid_input(a as int, b as int, c as int, d as int),
  ensures
      result as int >= 0,
      result as int == f(b as int, c as int, d as int) - f((a as int) - 1, c as int, d as int),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}