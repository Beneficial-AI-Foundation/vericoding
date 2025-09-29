// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= b <= a <= 20 && 1 <= c <= 20
}

spec fn remaining_water(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 { remaining } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use i64 for runtime arithmetic and clamp to i8 */
fn clamp_to_i8(x: i64) -> i8 {
    if x < -128 { -128i8 } else if x > 127 { 127i8 } else { x as i8 }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use i64 for arithmetic and clamp result to i8 */
    if input.len() < 3 {
        return Vec::<i8>::new();
    }
    let a = input[0] as i64;
    let b = input[1] as i64;
    let c = input[2] as i64;
    let available = a - b;
    let mut remaining = c - available;
    if remaining < 0 {
        remaining = 0;
    }
    let out = clamp_to_i8(remaining);
    let mut res: Vec<i8> = Vec::new();
    res.push(out);
    res
}
// </vc-code>


}

fn main() {}