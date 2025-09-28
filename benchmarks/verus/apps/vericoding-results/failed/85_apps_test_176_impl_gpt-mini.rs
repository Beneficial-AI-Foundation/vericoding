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
{
    let k_int: int = k as int;
    let a_int: int = a as int;
    let b_int: int = b as int;
    let mut i: int = a_int;
    let mut cnt: int = 0;
    while i <= b_int
        invariant
            a_int <= i,
            cnt == count_divisibles_in_range(k_int, a_int, i - 1),
        decreases b_int - i + 1
    {
        if i % k_int == 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    let res_i8: i8 = cnt as i8;
    res_i8
}
// </vc-code>


}

fn main() {}