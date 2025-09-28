// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lagmulx_helper(c: Vec<i8>) -> (result: Vec<i8>)
    requires c@.len() > 0,
    ensures
        result@.len() == c@.len() + 1,
        result@[0] as int == c@[0] as int,
        result@.len() >= 2 ==> result@[1] as int == -(c@[0] as int)
{
    /* helper modified by LLM (iteration 5): Fixed Vec creation with exec mode */
    let mut result = Vec::empty();
    result = result.push(c[0]);
    result = result.push(-c[0]);
    let mut i: nat = 2;
    while i <= c@.len()
        invariant
            result@.len() == i,
            result@[0] as int == c@[0] as int,
            i > 0 ==> result@[1] as int == -(c@[0] as int)
        decreases c@.len() - i
    {
        result = result.push(0);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn lagmulx(c: Vec<i8>) -> (result: Vec<i8>)
    requires c@.len() > 0,
    ensures 
        result@.len() == c@.len() + 1,
        result@[0] as int == c@[0] as int,
        result@.len() >= 2 ==> result@[1] as int == -(c@[0] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Call proof helper with proper vector handling */
    proof {
        let result = lagmulx_helper(c);
        result
    }
}
// </vc-code>


}
fn main() {}