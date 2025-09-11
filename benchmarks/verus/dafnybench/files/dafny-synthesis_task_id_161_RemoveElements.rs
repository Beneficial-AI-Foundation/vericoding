// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a@.index(i) == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)

    ensures 
        forall|x: i32| result@.contains(x) ==> in_array(a, x) && !in_array(b, x),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@.index(i) != result@.index(j)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}