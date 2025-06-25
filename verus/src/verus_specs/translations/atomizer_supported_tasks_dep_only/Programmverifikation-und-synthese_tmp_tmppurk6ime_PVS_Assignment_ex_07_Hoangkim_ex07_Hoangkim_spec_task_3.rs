pub fn swap(a: &mut [i32], i: usize, j: usize)
    requires(
        a.len() > 0 && i < a.len() && j < a.len()
    )
    ensures(|a: &mut [i32]|
        a[i] == old(a)[j] &&
        a[j] == old(a)[i]
    )
{
}

pub fn FindMin(a: &[i32], lo: usize) -> (minIdx: usize)
    requires(
        a.len() > 0 && lo < a.len()
    )
    ensures(|minIdx: usize|
        lo <= minIdx && minIdx < a.len() &&
        forall|x: usize| lo <= x && x < a.len() ==> a[minIdx] <= a[x]
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