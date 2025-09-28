// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(k: int, a: int, b: int) -> bool {
  k > 0 && a <= b
}

spec fn floor_div(a: int, b: int) -> int {
  if a >= 0 { a / b }
  else { (a - b + 1) / b }
}

spec fn count_divisibles_in_range(k: int, a: int, b: int) -> int {
  floor_div(b, k) - floor_div(a - 1, k)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8) -> (result: i8)
  requires
    valid_input(k as int, a as int, b as int),
  ensures
    result >= 0,
    result as int == count_divisibles_in_range(k as int, a as int, b as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant, loop logic, and overflow issues */
{
    let mut count: i32 = 0;
    let mut i: i32 = a as i32;
    while i <= b as i32
        invariant
            (a as i32) <= i <= (b as i32) + 1,
            count == count_divisibles_in_range(k as int, a as int, (i as int) - 1),
        decreases ((b as i32) - i as i32)
    {
        if i % (k as i32) == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}