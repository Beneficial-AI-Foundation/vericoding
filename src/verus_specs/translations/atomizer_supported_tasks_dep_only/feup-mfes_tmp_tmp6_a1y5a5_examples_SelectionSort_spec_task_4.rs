use vstd::prelude::*;

verus! {

pub fn findMin(a: &mut Vec<f64>, from: usize, to: usize) -> (index: usize)
    requires(
        0 <= from < to <= a.len()
    )
    ensures(|index: usize|
        from <= index < to &&
        forall|k: usize| from <= k < to ==> a[k] >= a[index as int]
    )
{
}

pub fn testFindMin()
{
}

}