pub fn pairwise_addition(a: &[i32]) -> Vec<i32>
    requires a.len() % 2 == 0
    ensures |result: Vec<i32>| result.len() == a.len() / 2
    ensures |result: Vec<i32>| forall|i: usize| 0 <= i < result.len() ==> result[i] == a[2*i] + a[2*i + 1]
{
}