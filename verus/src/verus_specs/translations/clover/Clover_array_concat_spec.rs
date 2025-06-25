pub fn concat(a: &[i32], b: &[i32]) -> Vec<i32>
    ensures(|result: Vec<i32>| result.len() == b.len() + a.len())
    ensures(|result: Vec<i32>| forall|k: usize| 0 <= k < a.len() ==> result[k] == a[k])
    ensures(|result: Vec<i32>| forall|k: usize| 0 <= k < b.len() ==> result[k + a.len()] == b[k])
{
}