pub fn is_sorted(a: &[i32]) -> (sorted: bool)
    requires(a.len() > 0)
    ensures(sorted <== forall|i: usize, j: usize| 0 <= i < j < a.len() ==> a[i] <= a[j])
    ensures(!sorted ==> exists|i: usize, j: usize| 0 <= i < j < a.len() && a[i] > a[j])
{
}