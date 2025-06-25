pub fn ordenar_mergesort(V: &mut [i32])
    requires(V.len() > 0)
{
}

pub fn mergesort(V: &mut [i32], c: usize, f: usize)
    requires(
        V.len() > 0 &&
        c >= 0 && f <= V.len()
    )
{
}

pub fn mezclar(V: &mut [i32], c: usize, m: usize, f: usize)
    requires(
        V.len() > 0 &&
        c <= m && m <= f &&
        0 <= c && c <= V.len() &&
        0 <= m && m <= V.len() &&
        0 <= f && f <= V.len()
    )
{
}