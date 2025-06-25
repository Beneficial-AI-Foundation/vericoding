pub fn has_common_element(a: &[i32], b: &[i32]) -> bool
    requires(a.len() > 0 && b.len() > 0)
    ensures(|result: bool| result ==> exists|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j])
    ensures(|result: bool| !result ==> forall|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j])
{
}