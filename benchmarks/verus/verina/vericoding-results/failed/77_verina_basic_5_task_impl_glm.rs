// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn abs(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant syntax by adding parentheses around the invariant block */
{
    let mut result = 0;
    let mut count: nat = 0;
    let abs_b: nat = if b < 0 { (-b) as nat } else { b as nat };
    
    while count < abs_b
        invariant ({
            result == a * (count as i32),
            0 <= count && count <= abs_b
        })
    {
        result += a;
        count += 1;
    }
    
    if b < 0 {
        -result
    } else {
        result
    }
}
// </vc-code>

}
fn main() {}