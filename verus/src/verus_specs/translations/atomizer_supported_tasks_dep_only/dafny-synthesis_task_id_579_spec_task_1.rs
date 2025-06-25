use vstd::prelude::*;

verus! {

spec fn InArray(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i as int] == x
}

pub fn DissimilarElements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are either in a or b, but not in both or neither
        forall|x: i32| result@.contains(x) ==> (InArray(a, x) != InArray(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
{
}

}