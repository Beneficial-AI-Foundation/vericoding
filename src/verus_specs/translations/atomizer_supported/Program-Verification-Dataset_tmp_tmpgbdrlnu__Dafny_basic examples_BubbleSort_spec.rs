pub fn sorted(a: &[i32], from: usize, to: usize) -> bool
    requires(
        from <= to && to <= a.len()
    )
{
    forall|u: usize, v: usize| from <= u && u < v && v < to ==> a[u] <= a[v]
}

pub fn pivot(a: &[i32], to: usize, pvt: usize) -> bool
    requires(
        pvt < to && to <= a.len()
    )
{
    forall|u: usize, v: usize| u < pvt && pvt < v && v < to ==> a[u] <= a[v]
}

pub fn bubbleSort(a: &mut [i32])
    requires(
        a.len() > 0
    )
    ensures(
        sorted(a, 0, a.len()) &&
        multiset(a@) == multiset(old(a)@)
    )
{
}