pub fn Max(a: &[nat]) -> (m: int)
    requires(true)
    ensures(|result: int| a.len() > 0 ==> forall|k: int| 0 <= k < a.len() ==> result >= a[k])
    ensures(|result: int| a.len() == 0 ==> result == -1)
    ensures(|result: int| a.len() > 0 ==> exists|i: int| 0 <= i < a.len() && result == a[i])
{
}