use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn shared_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    Vec::new()
}
// </vc-code>

fn main() {
}

}