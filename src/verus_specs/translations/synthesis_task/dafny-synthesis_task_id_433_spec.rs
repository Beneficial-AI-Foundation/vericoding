pub fn IsGreater(n: int, a: &[int]) -> (result: bool)
    requires(true)
    ensures(result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i as usize])
    ensures(!result ==> exists|i: int| 0 <= i < a.len() && n <= a[i as usize])
{
}