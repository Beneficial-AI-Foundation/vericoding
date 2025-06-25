spec fn preserved(a: &[i32], left: usize, right: usize) -> bool {
    left <= right && right <= a.len() &&
    a[left..right].to_multiset() == old(a)[left..right].to_multiset()
}

spec fn ordered(a: &[i32], left: usize, right: usize) -> bool
    requires left <= right <= a.len()
{
    forall|i: usize| 0 < left <= i < right ==> a[i-1] <= a[i]
}

spec fn sorted(a: &[i32]) -> bool {
    ordered(a, 0, a.len()) && preserved(a, 0, a.len())
}

pub fn selection_sort(a: &mut [i32])
    ensures sorted(a)
{
}