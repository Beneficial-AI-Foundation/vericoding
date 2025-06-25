pub fn selection_sort(a: &mut [i32])
    requires true
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures multiset(a@) == old(multiset(a@))
{
}

pub open spec fn swap_frame(a: &[i32], old_a: &[i32], lo: int, hi: int) -> bool
    recommends 0 <= lo <= hi <= a.len()
{
    (forall|i: int| 0 <= i < lo || hi <= i < a.len() ==> a[i] == old_a[i]) && multiset(a@) == multiset(old_a@)
}