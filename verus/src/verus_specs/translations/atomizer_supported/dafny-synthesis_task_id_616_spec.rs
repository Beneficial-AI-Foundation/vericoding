pub fn element_wise_modulo(a: &[i32], b: &[i32]) -> Vec<i32>
    requires
        a.len() == b.len(),
        forall|i: usize| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        |result: Vec<i32>| 
            result.len() == a.len() &&
            forall|i: usize| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
{
}