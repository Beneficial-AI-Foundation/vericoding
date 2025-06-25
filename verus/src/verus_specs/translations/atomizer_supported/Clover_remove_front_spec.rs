pub fn remove_front(a: &[i32]) -> (c: Vec<i32>)
    requires(a.len() > 0)
    ensures(a[1..] == c[..])
{
}