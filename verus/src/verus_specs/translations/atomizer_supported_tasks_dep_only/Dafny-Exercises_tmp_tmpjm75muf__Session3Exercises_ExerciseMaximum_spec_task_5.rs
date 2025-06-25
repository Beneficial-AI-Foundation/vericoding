pub fn mmaximum1(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 0 <= i < v.len()
    ensures forall|k: usize| 0 <= k < v.len() ==> v[i as int] >= v[k as int]
{
}

pub fn mmaxvalue1(v: &[i32]) -> (m: i32)
    requires v.len() > 0
    ensures exists|k: usize| 0 <= k < v.len() && m == v[k as int]
    ensures forall|k: usize| 0 <= k < v.len() ==> m >= v[k as int]
{
}