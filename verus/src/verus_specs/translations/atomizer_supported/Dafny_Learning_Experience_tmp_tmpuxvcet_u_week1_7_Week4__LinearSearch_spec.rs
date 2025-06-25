pub fn LinearSeach0<T>(a: &[T], P: impl Fn(T) -> bool) -> (n: usize)
    ensures(0 <= n <= a.len())
    ensures(n == a.len() || P(a[n]))
{
}

pub fn P(n: i32) -> bool {
    n % 2 == 0
}

pub fn TestLinearSearch() {
}

pub fn LinearSeach1<T>(a: &[T], P: impl Fn(T) -> bool) -> (n: usize)
    ensures(0 <= n <= a.len())
    ensures(n == a.len() || P(a[n]))
    ensures(n == a.len() ==> forall|i: usize| 0 <= i < a.len() ==> !P(a[i]))
{
}