pub fn find_min_index(a: &[i32], s: usize, e: usize) -> (min_i: usize)
    requires(
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    )
    ensures(|min_i: usize|
        min_i >= s &&
        min_i < e &&
        forall|k: usize| s <= k && k < e ==> a[min_i as int] <= a[k as int]
    )
{
}