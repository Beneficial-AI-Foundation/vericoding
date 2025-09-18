// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to check safe division and addition */
spec fn can_safely_divide(numerator: i32, denominator: i32) -> bool {
    denominator != 0 && !(numerator == i32::MIN && denominator == -1)
}
spec fn can_safely_add(a: i32, b: i32) -> bool {
    (b >= 0 && a <= i32::MAX - b) || (b < 0 && a >= i32::MIN - b)
}
// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i32>) -> (roots: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] == 1 + c@[0] / c@[1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added safety checks for division and addition */
{
    if c.len() == 2 {
        let last = c[c.len()-1];
        if can_safely_divide(c[0], last) {
            let quotient = c[0] / last;
            if can_safely_add(1, quotient) {
                let root = 1 + quotient;
                vec![root]
            } else {
                vec![]
            }
        } else {
            vec![]
        }
    } else {
        vec![]
    }
}
// </vc-code>

}
fn main() {}