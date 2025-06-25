pub fn appendArray(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(true)
    ensures(|result: Vec<i32>| result.len() == a.len() + b.len())
    ensures(|result: Vec<i32>| forall|i: usize| 0 <= i < a.len() ==> a[i] == result[i])
    ensures(|result: Vec<i32>| forall|i: usize| 0 <= i < b.len() ==> b[i] == result[a.len() + i])
{
}