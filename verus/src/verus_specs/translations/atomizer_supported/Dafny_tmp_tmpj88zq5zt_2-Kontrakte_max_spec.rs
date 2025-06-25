pub fn max(a: &[i32], b: &[i32], i: usize, j: usize) -> (m: i32)
    requires(
        i < a.len() &&
        j < b.len()
    )
    ensures(|m: i32|
        (a[i as int] > b[j as int] ==> m == a[i as int]) &&
        (a[i as int] <= b[j as int] ==> m == b[j as int])
    )
{
}

pub fn testMax(a: &[i32], b: &[i32], i: usize, j: usize)
    requires(
        i < a.len() &&
        j < b.len()
    )
{
}