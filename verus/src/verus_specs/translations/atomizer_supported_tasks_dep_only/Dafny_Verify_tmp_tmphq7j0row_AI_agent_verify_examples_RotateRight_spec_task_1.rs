pub fn rotate_right(a: &mut [i32])
    requires(a.len() > 0)
    ensures(forall|i: usize| 1 <= i < a.len() ==> a[i] == old(a)[(i-1)])
    ensures(a[0] == old(a)[a.len()-1])
{
}