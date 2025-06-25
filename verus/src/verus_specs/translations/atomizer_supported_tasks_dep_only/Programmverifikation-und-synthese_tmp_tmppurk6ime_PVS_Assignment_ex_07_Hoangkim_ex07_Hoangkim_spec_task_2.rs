pub fn find_min(a: &[i32], lo: usize) -> (minIdx: usize)
    requires(
        a.len() > 0 && lo < a.len()
    )
    ensures(|minIdx: usize|
        lo <= minIdx && minIdx < a.len() &&
        forall|x: usize| lo <= x && x < a.len() ==> a[minIdx as int] <= a[x as int]
    )
{
}