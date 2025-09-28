// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeweight(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let result = x.clone();
    result
}
// </vc-code>


}
fn main() {}