pub fn incrementArray(a: &mut [i32])
    requires(a.len() > 0)
    ensures(forall|i: usize| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1)
{
}