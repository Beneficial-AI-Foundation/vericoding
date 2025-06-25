pub fn invert_array(a: &mut [i32])
    requires(
        true
    )
    ensures(
        forall|i: usize| 0 <= i < a.len() ==> a[i] == old(a)[a.len()-1-i]
    )
{
}