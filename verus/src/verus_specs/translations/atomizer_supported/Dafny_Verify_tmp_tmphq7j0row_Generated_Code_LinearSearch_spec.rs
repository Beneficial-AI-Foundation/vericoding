pub fn linear_search<T>(a: &[T], p: impl Fn(&T) -> bool) -> (n: usize)
    ensures(
        n <= a.len(),
        n == a.len() || p(&a[n as int]),
        forall|i: int| 0 <= i < n ==> !p(&a[i]),
    )
{
}