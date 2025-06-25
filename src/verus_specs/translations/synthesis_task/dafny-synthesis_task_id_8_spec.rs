pub fn square_elements(a: &[i32]) -> (squared: Vec<i32>)
    ensures
        squared.len() == a.len(),
        forall|i: usize| 0 <= i < a.len() ==> squared[i] == a[i] * a[i],
{
}