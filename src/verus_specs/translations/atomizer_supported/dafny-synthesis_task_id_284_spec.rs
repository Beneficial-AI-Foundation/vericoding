pub fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    requires(true)
    ensures(result ==> forall|i: usize| 0 <= i < a.len() ==> a[i] == n)
    ensures(!result ==> exists|i: usize| 0 <= i < a.len() && a[i] != n)
{
}