pub fn arrayProduct(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(a.len() == b.len())
    ensures(|c: Vec<i32>| c.len() == a.len())
    ensures(|c: Vec<i32>| forall|i: usize| 0 <= i && i < a.len() ==> a[i] * b[i] == c[i])
{
}