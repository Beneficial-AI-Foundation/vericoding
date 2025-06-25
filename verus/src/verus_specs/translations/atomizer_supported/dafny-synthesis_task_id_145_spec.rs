pub fn max_difference(a: &[i32]) -> (diff: i32)
    requires(a.len() > 1)
    ensures(forall|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff)
{
}