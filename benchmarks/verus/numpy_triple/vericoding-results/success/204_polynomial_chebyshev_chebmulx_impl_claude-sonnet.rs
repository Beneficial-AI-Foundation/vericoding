// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebmulx(c: Vec<i8>) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(0i8);
    for i in 0..c.len()
        invariant
            result.len() == i + 1,
    {
        result.push(c[i]);
    }
    result
}
// </vc-code>

}
fn main() {}