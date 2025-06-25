use vstd::prelude::*;

verus! {

spec fn preserved(a_old: &[i32], a_new: &[i32], left: usize, right: usize) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

spec fn sorted(a_old: &[i32], a_new: &[i32]) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len()) && preserved(a_old, a_new, 0, a_new.len())
}

pub fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(&old(a), a)
{
}

}