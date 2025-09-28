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

/* helper modified by LLM (iteration 4): fixed type handling and added proper ghost variable declarations */
proof fn floor_div_spec(a: int, b: int) -> int
  requires
    b > 0,
  ensures
    result == floor_div(a, b),
{
  if a >= 0 {
    a / b
  } else {
    (a - b + 1) / b
  }
}

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
    /* code modified by LLM (iteration 4): fixed ghost variables and result handling */
    ghost {
        let k_int = k as int;
        let a_int = a as int;
        let b_int = b as int;
    }
    
    let mut result: i8 = 0;
    let mut current = a;
    
    while current <= b
        invariant
            result >= 0,
            current >= a,
            current <= b + 1,
            result as int == count_divisibles_in_range(k as int, a as int, (current as int) - 1),
        decreases (b - current + 1) as int,
    {
        if current % k == 0 {
            result = result + 1;
        }
        current = current + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}