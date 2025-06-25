// ATOM 
spec fn contains(v: int, a: &[int], n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j as nat] == v
}

// ATOM 
spec fn upper_bound(v: int, a: &[int], n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j as nat] <= v
}

// ATOM 
spec fn is_max(m: int, a: &[int], n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// SPEC 
pub fn max(a: &[int], n: int) -> (max: int)
    requires(
        0 < n <= a.len()
    )
    ensures(|max: int|
        is_max(max, a, n)
    )
{
}