pub fn find_min_index(a: &[i32], s: usize, e: usize) -> (min_i: usize)
    requires(
        a.len() > 0 &&
        s < a.len() &&
        e <= a.len() &&
        e > s
    )
    ensures(|min_i: usize|
        min_i >= s &&
        min_i < e &&
        forall|k: usize| s <= k < e ==> a[min_i as int] <= a[k as int]
    )
{
}

spec fn is_sorted(ss: Seq<i32>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
{
    a.len() == b.len() &&
    ((a.len() == 0 && b.len() == 0) ||
    exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
    is_permutation(a.subrange(0, i) + (if i < a.len() { a.subrange(i+1, a.len() as int) } else { seq![] }),
                   b.subrange(0, j) + (if j < b.len() { b.subrange(j+1, b.len() as int) } else { seq![] })))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool
{
    a.to_multiset() == b.to_multiset()
}

pub fn selection_sort(ns: &mut [i32])
    requires(ns.len() >= 0)
    ensures(
        is_sorted(ns@) &&
        is_permutation2(old(ns)@, ns@)
    )
{
}