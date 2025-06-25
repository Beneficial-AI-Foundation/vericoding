pub fn selection_sort(a: &mut [i32])
    ensures(
        sorted(a) && multiset(a@) == multiset(old(a)@)
    )
{
}

spec fn sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}