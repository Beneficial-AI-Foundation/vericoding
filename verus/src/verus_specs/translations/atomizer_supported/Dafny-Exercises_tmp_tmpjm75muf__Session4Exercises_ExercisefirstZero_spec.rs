pub fn mfirstCero(v: &[i32]) -> (i: usize)
    requires(true)
    ensures(|result: usize| 0 <= result <= v.len())
    ensures(|result: usize| forall|j: usize| 0 <= j < result ==> v[j] != 0)
    ensures(|result: usize| result != v.len() ==> v[result] == 0)
{
}