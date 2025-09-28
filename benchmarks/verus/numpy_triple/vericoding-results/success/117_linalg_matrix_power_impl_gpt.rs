// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_square(a: Vec<Vec<i8>>) -> bool {
    a.len() > 0 && forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len()
}
// </vc-helpers>

// <vc-spec>
fn matrix_power(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() == a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i].len() == a.len(),
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}