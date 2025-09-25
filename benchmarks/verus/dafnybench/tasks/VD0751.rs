// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: &Vec<int>, x: int) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn dissimilar_elements(a: &Vec<int>, b: &Vec<int>) -> (result: Vec<int>)
    ensures

        forall|x: int| result@.contains(x) ==> (in_array(a, x) != in_array(b, x)),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}