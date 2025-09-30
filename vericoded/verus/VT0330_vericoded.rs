// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_i8(v: i8) -> (res: i8)
    ensures
        res == v,
        v == 0 ==> res == 0,
{
    v
}
// </vc-helpers>

// <vc-spec>
fn log1p(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] as int > -1,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() && x[i] as int == 0 ==> result[i] as int == 0,
// </vc-spec>
// <vc-code>
{
    let result = x;
    result
}
// </vc-code>


}
fn main() {}