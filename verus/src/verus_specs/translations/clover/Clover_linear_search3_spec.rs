pub fn linear_search_3<T>(a: &[T], P: impl Fn(&T) -> bool) -> (n: usize)
    requires(exists|i: usize| 0 <= i < a.len() && P(&a[i]))
    ensures(|n: usize| 0 <= n < a.len() && P(&a[n]))
    ensures(|n: usize| forall|k: usize| 0 <= k < n ==> !P(&a[k]))
{
}