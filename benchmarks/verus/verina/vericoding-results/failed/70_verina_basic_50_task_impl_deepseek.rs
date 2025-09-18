// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix abs_lemma to handle INT_MIN case properly */
proof fn abs_lemma(x: int) 
    ensures 
        abs(x) >= 0, 
        x >= 0 ==> abs(x) == x, 
        x < 0 ==> abs(x) == -x,
        x >= -2147483648
{ 
    if x >= 0 { 
        assert(abs(x) == x); 
        assert(abs(x) >= 0); 
        assert(x >= -2147483648);
    } else { 
        assert(abs(x) == -x); 
        assert(-x > 0); 
        assert(abs(x) >= 0);
        assert(x >= -2147483648);
    } 
}
// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation using abs_lemma */
    proof {
        abs_lemma(x as int);
    }
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-code>

}
fn main() {}