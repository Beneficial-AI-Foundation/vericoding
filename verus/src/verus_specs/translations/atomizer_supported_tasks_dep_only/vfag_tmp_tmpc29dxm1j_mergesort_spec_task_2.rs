pub fn mergesort(V: &mut Vec<i32>, c: usize, f: usize)
    requires(
        c >= 0 && f <= V.len()
    )
    ensures(
        V.len() == old(V).len()
    )
{
}

pub fn mezclar(V: &mut Vec<i32>, c: usize, m: usize, f: usize)
    requires(
        c <= m <= f &&
        0 <= c <= V.len() &&
        0 <= m <= V.len() &&
        0 <= f <= V.len()
    )
    ensures(
        V.len() == old(V).len()
    )
{
}