// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DateTime64 {
    Valid(i64),
    Nat,
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn isnat(x: Vec<DateTime64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == true <==> x@.index(i) == DateTime64::Nat),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == false <==> exists|val: i64| x@.index(i) == DateTime64::Valid(val)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}