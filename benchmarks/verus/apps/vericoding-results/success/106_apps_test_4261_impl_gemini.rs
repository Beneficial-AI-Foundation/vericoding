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
/* helper modified by LLM (iteration 2): changed signature to use i8 instead of int for exec context */
fn calculate_remaining_water(a: i8, b: i8, c: i8) -> (rem: i8)
    requires
        valid_input(a as int, b as int, c as int),
    ensures
        rem as int == remaining_water(a as int, b as int, c as int),
        0 <= rem <= 20,
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 {
        remaining
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type errors by using i8 instead of ghost int */
{
    if input.len() == 3 {
        let a = input[0];
        let b = input[1];
        let c = input[2];
        if 1 <= b && b <= a && a <= 20 && 1 <= c && c <= 20 {
            let rem = calculate_remaining_water(a, b, c);
            return vec![rem];
        }
    }
    vec![]
}
// </vc-code>


}

fn main() {}