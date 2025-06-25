pub fn swap(a: &mut [i32], i: usize, j: usize)
    requires(
        a.len() > 0 && i < a.len() && j < a.len()
    )
    ensures(|a_new: &mut [i32]|
        a_new[i as int] == old(a)[j as int] &&
        a_new[j as int] == old(a)[i as int]
    )
{
}

pub fn FindMin(a: &[i32], lo: usize) -> usize
    requires(
        a.len() > 0 && lo < a.len()
    )
    ensures(|minIdx: usize|
        lo <= minIdx && minIdx < a.len() &&
        forall|x: usize| lo <= x && x < a.len() ==> a[minIdx as int] <= a[x as int]
    )
{
}

pub open spec fn sorted(a: Seq<i32>) -> bool
{
    forall|i: int| 0 < i < a.len() ==> a[i-1] <= a[i]
}

pub fn selectionSort(a: &mut [i32])
{
}