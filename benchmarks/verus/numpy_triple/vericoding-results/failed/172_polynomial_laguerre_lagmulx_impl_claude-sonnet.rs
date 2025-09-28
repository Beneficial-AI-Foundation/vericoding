// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fix nat literal syntax error */
    let mut result = Vec::new();
    result.push(c[0]);
    
    if c@.len() >= 1 {
        if c[0] == i8::MIN {
            result.push(i8::MAX);
        } else {
            result.push(-c[0]);
        }
    }
    
    let mut i = 1;
    while i < c.len()
        invariant
            result@.len() == i + 1,
            result@[0] as int == c@[0] as int,
            result@.len() >= 2 ==> result@[1] as int == -(c@[0] as int),
            i <= c@.len(),
        decreases c@.len() - i
    {
        result.push(0);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}