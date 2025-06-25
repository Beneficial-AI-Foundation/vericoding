pub fn mfirstMaximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 0 <= i < v.len()
    ensures forall|k: usize| 0 <= k < v.len() ==> v[i as int] >= v[k as int]
    ensures forall|l: usize| 0 <= l < i ==> v[i as int] > v[l as int]
{
}