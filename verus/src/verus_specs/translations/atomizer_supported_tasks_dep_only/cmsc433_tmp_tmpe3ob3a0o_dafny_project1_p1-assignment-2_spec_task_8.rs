pub fn Reverse(a: &[i32]) -> (aRev: Vec<i32>)
    requires(true)
    ensures(|result: Vec<i32>| result.len() == a.len())
    ensures(|result: Vec<i32>| forall|i: int| 0 <= i < a.len() ==> a[i as usize] == result[(result.len() - i - 1) as usize])
{
}