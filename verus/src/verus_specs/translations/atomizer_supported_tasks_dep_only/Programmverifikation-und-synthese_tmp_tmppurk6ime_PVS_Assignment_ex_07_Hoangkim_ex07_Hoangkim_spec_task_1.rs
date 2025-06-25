pub fn swap(a: &mut Vec<i32>, i: usize, j: usize)
    requires(
        a.len() > 0 && i < a.len() && j < a.len()
    )
    ensures(
        a[i as int] == old(a)[j as int] &&
        a[j as int] == old(a)[i as int]
    )
{
}