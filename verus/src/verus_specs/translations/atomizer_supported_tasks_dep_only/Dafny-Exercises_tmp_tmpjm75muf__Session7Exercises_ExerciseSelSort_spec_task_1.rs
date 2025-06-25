// ATOM 
spec fn sorted_seg(a: &[i32], i: usize, j: usize) -> bool
{
    0 <= i <= j <= a.len() &&
    forall|l: usize, k: usize| i <= l <= k < j ==> a[l] <= a[k]
}

// SPEC 
pub fn selSort(a: &mut [i32], c: usize, f: usize)
    requires(0 <= c <= f <= a.len())
    ensures(sorted_seg(a, c, f))
    ensures(a.subrange(c, f).to_multiset() == old(a).subrange(c, f).to_multiset())
    ensures(a.subrange(0, c) == old(a).subrange(0, c) && a.subrange(f, a.len()) == old(a).subrange(f, old(a).len()))
{
}