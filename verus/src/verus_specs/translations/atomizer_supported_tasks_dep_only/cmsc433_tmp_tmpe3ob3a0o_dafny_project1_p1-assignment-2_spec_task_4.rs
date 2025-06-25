pub fn ArraySum(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(a.len() == b.len())
    ensures(|c: Vec<i32>| c.len() == a.len() && 
        forall|i: int| 0 <= i < c.len() ==> c[i] == a[i] + b[i])
{
}