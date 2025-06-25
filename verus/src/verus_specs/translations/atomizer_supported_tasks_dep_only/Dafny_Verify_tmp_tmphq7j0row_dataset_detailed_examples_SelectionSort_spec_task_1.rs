pub fn selection_sort(a: &mut [i32])
    ensures(
        forall|i: usize, j: usize| 0 <= i < j < a.len() ==> a[i] <= a[j]
    )
    ensures(
        multiset(a@) == old(multiset(a@))
    )
{
}