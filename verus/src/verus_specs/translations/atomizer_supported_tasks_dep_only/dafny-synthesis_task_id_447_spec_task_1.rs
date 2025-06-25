pub fn CubeElements(a: &[i32]) -> (cubed: Vec<i32>)
    requires(true)
    ensures(|cubed: Vec<i32>| cubed.len() == a.len())
    ensures(|cubed: Vec<i32>| forall|i: usize| 0 <= i < a.len() ==> cubed[i] == a[i] * a[i] * a[i])
{
}