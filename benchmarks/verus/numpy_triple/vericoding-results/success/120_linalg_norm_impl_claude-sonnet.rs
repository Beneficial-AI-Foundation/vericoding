// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added overflow check for abs function */
fn abs_i8(x: i8) -> (result: i8)
    requires
        x != i8::MIN,
    ensures
        result >= 0,
        result == x || result == -x,
{
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-helpers>

// <vc-spec>
fn norm(x: Vec<i8>) -> (result: i8)
    requires true,
    ensures true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added precondition check for abs_i8 */
    let mut max_val: i8 = 0;
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            max_val >= 0,
        decreases x.len() - i
    {
        if x[i] != i8::MIN {
            if abs_i8(x[i]) > max_val {
                max_val = abs_i8(x[i]);
            }
        }
        i += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}