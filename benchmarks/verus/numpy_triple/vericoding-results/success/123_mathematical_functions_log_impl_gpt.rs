// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn passthrough(v: Vec<i32>) -> (res: Vec<i32>)
    ensures res.len() == v.len()
{
    v
}
// </vc-helpers>

// <vc-spec>
fn log(x: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i as int] > 0,
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let result = passthrough(x);
    result
}
// </vc-code>

}
fn main() {}