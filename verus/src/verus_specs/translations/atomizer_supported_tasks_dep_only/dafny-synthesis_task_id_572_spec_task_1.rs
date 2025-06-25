pub fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires(true)
    ensures(forall|x: i32| result@.contains(x) <==> exists|i: usize| 0 <= i < a.len() && a[i] == x)
    ensures(forall|i: usize, j: usize| 0 <= i < j < result@.len() ==> result@[i] != result@[j])
{
}