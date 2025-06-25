pub fn element_wise_subtraction(a: &[i32], b: &[i32]) -> Vec<i32>
    requires(a.len() == b.len())
    ensures(|result: Vec<i32>| result.len() == a.len())
    ensures(|result: Vec<i32>| forall|i: usize| 0 <= i < result.len() ==> result[i] == a[i] - b[i])
{
}