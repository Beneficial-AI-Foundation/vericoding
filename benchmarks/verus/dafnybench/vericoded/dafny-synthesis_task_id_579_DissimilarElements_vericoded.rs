use vstd::prelude::*;

verus! {

spec fn in_array(a: &Vec<int>, x: int) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn dissimilar_elements(a: &Vec<int>, b: &Vec<int>) -> (result: Vec<int>)
    ensures
        // All elements in the output are either in a or b, but not in both or neither
        forall|x: int| result@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// <vc-code>
{
    Vec::new()
}
// </vc-code>

fn main() {}

}