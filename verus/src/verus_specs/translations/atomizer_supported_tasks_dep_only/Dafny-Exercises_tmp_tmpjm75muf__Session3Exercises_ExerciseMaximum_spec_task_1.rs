pub fn mmaximum1(v: &[i32]) -> (i: usize)
    requires(v.len() > 0)
    ensures(i < v.len())
    ensures(forall|k: usize| k < v.len() ==> v[i as int] >= v[k as int])
{
}