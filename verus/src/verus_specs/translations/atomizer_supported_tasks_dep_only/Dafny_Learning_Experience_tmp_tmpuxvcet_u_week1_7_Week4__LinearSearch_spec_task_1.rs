pub fn LinearSeach0<T>(a: &[T], P: impl Fn(&T) -> bool) -> (n: usize)
    ensures(
        n <= a.len() &&
        (n == a.len() || P(&a[n]))
    )
{
}

pub closed spec fn P(n: int) -> bool {
    n % 2 == 0
}