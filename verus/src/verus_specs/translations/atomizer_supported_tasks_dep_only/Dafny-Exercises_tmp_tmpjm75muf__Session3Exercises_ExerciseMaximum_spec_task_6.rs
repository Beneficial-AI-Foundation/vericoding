pub fn mmaximum2(v: &[int]) -> (i: usize)
    requires(v.len() > 0)
    ensures(|i: usize| 0 <= i < v.len())
    ensures(|i: usize| forall|k: usize| 0 <= k < v.len() ==> v[i] >= v[k])
{
}

pub fn mmaxvalue2(v: &[int]) -> (m: int)
    requires(v.len() > 0)
    ensures(|m: int| exists|k: usize| 0 <= k < v.len() && m == v[k])
    ensures(|m: int| forall|k: usize| 0 <= k < v.len() ==> m >= v[k])
{
}