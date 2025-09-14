// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut x: i32 = 0;
    let mut y: i32 = 0;
    
    while x < 5
        invariant
            x <= 5,
            y == x * 2,
        decreases 5 - x,
    {
        x = x + 1;
        y = y + 2;
    }
    
    assert(x == 5);
    assert(y == 10);
    
    let result = x + 4;
    assert(result == 9);
    assert(result < 10);
    
    result
}
// </vc-code>

}
fn main() {}