// ATOM 

spec fn P(n: int) -> bool {
    n % 2 == 0
}

// SPEC 

pub fn LinearSeach1<T>(a: &[T], P: spec_fn(T) -> bool) -> (n: usize)
    ensures
        0 <= n <= a.len(),
        n == a.len() || P(a[n as int]),
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> !P(a[i]),
{
}