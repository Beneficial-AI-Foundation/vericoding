pub fn linear_search3<T>(a: &[T], P: impl Fn(&T) -> bool) -> (n: usize)
    requires(
        exists|i: usize| 0 <= i && i < a.len() && P(&a[i])
    )
    ensures(|n: usize|
        0 <= n && n < a.len() && P(&a[n])
    )
    ensures(|n: usize|
        forall|k: usize| 0 <= k && k < n ==> !P(&a[k])
    )
{
}