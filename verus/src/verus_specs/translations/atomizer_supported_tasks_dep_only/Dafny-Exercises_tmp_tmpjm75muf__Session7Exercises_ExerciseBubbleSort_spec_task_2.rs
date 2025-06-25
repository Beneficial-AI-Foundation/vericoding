spec fn sorted_seg(a: &[int], i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

pub fn bubbleSort(a: &mut Vec<int>, c: usize, f: usize)
    requires(
        0 <= c <= f <= a.len()
    )
    ensures(
        sorted_seg(a, c as int, f as int) &&
        multiset(a.subrange(c as int, f as int)) == old(multiset(a.subrange(c as int, f as int))) &&
        a.subrange(0, c as int) == old(a.subrange(0, c as int)) &&
        a.subrange(f as int, a.len() as int) == old(a.subrange(f as int, a.len() as int))
    )
{
}