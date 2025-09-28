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
/* helper modified by LLM (iteration 2): Fixed return value naming for ensures clause */
fn compute_remaining(a: i8, b: i8, c: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int),
    ensures
        remaining_water(a as int, b as int, c as int) == result as int,
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 { remaining } else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Removed invalid spec type assignments in exec code, used i8 comparisons instead */
{
    let mut result = Vec::new();
    if input.len() >= 3 {
        let a = input[0];
        let b = input[1];
        let c = input[2];
        if 1 <= b && b <= a && a <= 20 && 1 <= c && c <= 20 {
            let r = compute_remaining(a, b, c);
            result.push(r);
        }
    }
    result
}
// </vc-code>


}

fn main() {}