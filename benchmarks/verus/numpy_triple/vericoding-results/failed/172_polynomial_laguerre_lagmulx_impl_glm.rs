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
/* code modified by LLM (iteration 5): fixed overflow and invariant issues */
{
    let n = c.len();
    let mut result = Vec::new();
    let first = c[0];
    assert(first != i8::MIN);
    result.push(first);
    result.push(-first);
    let mut i = 1;
    while i < n
        invariant
            n == c@.len(),
            result@.len() == 1 + i,
            result@[0] == c@[0],
            result@.len() >= 2 ==> result@[1] == -c@[0],
            1 <= i <= n,
        decreases n - i
    {
        result.push(c[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}