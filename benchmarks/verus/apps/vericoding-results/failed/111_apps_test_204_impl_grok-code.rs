// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, x: int, y: int) -> bool {
  a > 0 && b > 0 && x > 0 && y > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a >= 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn min(a: int, b: int) -> int {
  if a <= b { a } else { b }
}

spec fn expected_result(a: int, b: int, x: int, y: int) -> int
  recommends valid_input(a, b, x, y)
{
  let g = gcd(x, y);
  let x_reduced = x / g;
  let y_reduced = y / g;
  min(a / x_reduced, b / y_reduced)
}
// </vc-preamble>

// <vc-helpers>
fn gcd_exec(a0: u32, b0: u32) -> (res: u32)
    requires
        a0 >= 0,
        b0 >= 0,
    ensures
        res as int == gcd(a0 as int, b0 as int),
{
    let mut a: u32 = a0;
    let mut b: u32 = b0;
    while b != 0
        invariant
            gcd(a as int, b as int) == gcd(a0 as int, b0 as int),
        decreases b,
    {
        let temp = a % b;
        a = b;
        b = temp;
    }
    a
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8) -> (result: i8)
requires 
  valid_input(a as int, b as int, x as int, y as int)
ensures 
  result as int >= 0,
  result as int == expected_result(a as int, b as int, x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Used u32 for executable arithmetic to avoid ghost-only type restrictions */
    let xa: u32 = x as u32;
    let ya: u32 = y as u32;
    let aa: u32 = a as u32;
    let ba: u32 = b as u32;
    let g: u32 = gcd_exec(xa, ya);
    let x_reduced: u32 = xa / g;
    let y_reduced: u32 = ya / g;
    let res1: u32 = aa / x_reduced;
    let res2: u32 = ba / y_reduced;
    let result_u32 = if res1 <= res2 { res1 } else { res2 };
    result_u32 as i8
}
// </vc-code>


}

fn main() {}