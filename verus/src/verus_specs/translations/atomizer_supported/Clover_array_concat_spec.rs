pub fn concat(a: &[int], b: &[int]) -> (c: Vec<int>)
    ensures(c.len() == b.len() + a.len())
    ensures(forall|k: int| 0 <= k < a.len() ==> c[k] == a[k])
    ensures(forall|k: int| 0 <= k < b.len() ==> c[k + a.len()] == b[k])
{
}