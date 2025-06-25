pub fn findMax(a: &mut Vec<i32>, n: usize) -> (r: usize)
    requires(
        a.len() > 0,
        0 < n <= a.len(),
    )
    ensures(|r: usize|
        0 <= r < n <= a.len() &&
        forall|k: usize| 0 <= k < n <= a.len() ==> a[r] >= a[k] &&
        a@ == old(a)@
    )
{
}