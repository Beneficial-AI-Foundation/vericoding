pub fn find_max(a: &[int]) -> (max: usize)
    requires(
        a.len() > 0
    )
    ensures(|max: usize|
        0 <= max < a.len() &&
        forall|x: int| 0 <= x < a.len() ==> a[max] >= a[x]
    )
{
}