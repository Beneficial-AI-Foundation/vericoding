// ATOM 
spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: usize| 0 <= i < a.len() && a[i] == x
}

// SPEC
pub fn intersection(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
{
}