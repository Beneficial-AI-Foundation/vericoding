pub fn ordenar_mergesort(V: &mut Vec<i32>)
    requires(V.len() > 0)
{
}

pub fn mergesort(V: &mut Vec<i32>, c: usize, f: usize) 
    requires(
        V.len() > 0 &&
        c <= V.len() &&
        f <= V.len()
    )
{
}

pub fn mezclar(V: &mut Vec<i32>, c: usize, m: usize, f: usize)
    requires(
        V.len() > 0 &&
        c <= m && m <= f &&
        c <= V.len() &&
        m <= V.len() &&
        f <= V.len()
    )
{
}