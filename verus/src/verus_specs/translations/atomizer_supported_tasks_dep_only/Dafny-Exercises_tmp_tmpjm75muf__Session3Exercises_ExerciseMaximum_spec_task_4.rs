pub fn mlastMaximum(v: &[i32]) -> (i: usize)
    requires
        v.len() > 0,
    ensures
        0 <= i < v.len(),
        forall|k: usize| 0 <= k < v.len() ==> v[i as int] >= v[k as int],
        forall|l: usize| i < l < v.len() ==> v[i as int] > v[l as int],
{
}