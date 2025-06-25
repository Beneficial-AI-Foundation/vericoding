pub fn appendArray(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(true)
    ensures(|c: Vec<i32>| c.len() == a.len() + b.len())
    ensures(|c: Vec<i32>| forall|i: usize| 0 <= i < a.len() ==> a[i] == c[i])
    ensures(|c: Vec<i32>| forall|i: usize| 0 <= i < b.len() ==> b[i] == c[a.len() + i])
{
}