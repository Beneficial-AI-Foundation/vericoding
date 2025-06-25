pub fn rotate(a: &[i32], offset: i32) -> Vec<i32>
    requires(0 <= offset)
    ensures(|result: Vec<i32>| result.len() == a.len())
    ensures(|result: Vec<i32>| forall|i: usize| 0 <= i && i < a.len() ==> result[i] == a[(i + offset as usize) % a.len()])
{
}