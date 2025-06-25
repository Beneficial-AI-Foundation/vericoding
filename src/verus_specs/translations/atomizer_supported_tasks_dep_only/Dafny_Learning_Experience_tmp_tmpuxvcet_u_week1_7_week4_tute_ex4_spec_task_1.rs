pub fn LinearSearch<T>(a: &[T], P: impl Fn(&T) -> bool) -> (n: isize)
    ensures(
        -1 <= n < a.len() as isize,
        n == -1 || P(&a[n as usize]),
        n != -1 ==> forall|i: usize| 0 <= i < n as usize ==> !P(&a[i]),
        n == -1 ==> forall|i: usize| 0 <= i < a.len() ==> !P(&a[i]),
    )
{
}