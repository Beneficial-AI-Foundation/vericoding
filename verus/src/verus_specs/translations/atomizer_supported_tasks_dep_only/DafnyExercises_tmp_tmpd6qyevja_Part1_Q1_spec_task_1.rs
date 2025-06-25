pub fn addArrays(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(a.len() == b.len())
    ensures(|c: Vec<i32>| b.len() == c.len())
    ensures(|c: Vec<i32>| forall|i: int| 0 <= i < c.len() ==> c[i as usize] == a[i as usize] + b[i as usize])
{
}