pub fn linear_search<T>(a: &[T], p: impl Fn(&T) -> bool) -> (n: usize)
    requires(
        true
    )
    ensures(|n: usize|
        n <= a.len() &&
        (n == a.len() || p(&a[n])) &&
        forall|i: usize| 0 <= i < n ==> !p(&a[i])
    )
{
}