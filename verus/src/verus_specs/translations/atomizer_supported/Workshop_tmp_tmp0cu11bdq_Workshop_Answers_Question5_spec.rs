pub fn rev(a: &mut [i32])
    requires(true)
    ensures(forall|k: usize| 0 <= k < a.len() ==> a[k] == old(a)[(a.len() - 1) - k])
{
}