pub fn selection_sort(a: &mut [i32])
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        multiset(a@) == old(multiset(a@)),
{
}