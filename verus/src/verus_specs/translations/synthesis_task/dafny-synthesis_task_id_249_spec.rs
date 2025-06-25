// ATOM
pub open spec fn in_array(a: &[int], x: int) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// SPEC
pub fn intersection(a: &[int], b: &[int]) -> (result: Vec<int>)
    ensures
        // All elements in the output are in both a and b
        forall|x: int| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
}