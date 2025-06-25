pub fn bubble_sort(a: &mut Vec<int>)
    requires(true)
    ensures(forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j])
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}