pub fn find_max(a: &[i32]) -> (i: usize)
    requires(
        0 < a.len(),
    )
    ensures(|i: usize|
        0 <= i < a.len() &&
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int]
    )
{
}