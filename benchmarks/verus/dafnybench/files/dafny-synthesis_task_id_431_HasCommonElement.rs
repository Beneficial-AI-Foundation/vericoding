// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &[i32], b: &[i32]) -> (result: bool)
    ensures 
        result ==> (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) &&
        (!result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}