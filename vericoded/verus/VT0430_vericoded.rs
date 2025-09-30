// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn preserve_len(v: Vec<i8>) -> (r: Vec<i8>)
    ensures
        r.len() == v.len(),
{
    v
}
// </vc-helpers>

// <vc-spec>
fn hermeweight(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let r = preserve_len(x);
    r
}
// </vc-code>


}
fn main() {}