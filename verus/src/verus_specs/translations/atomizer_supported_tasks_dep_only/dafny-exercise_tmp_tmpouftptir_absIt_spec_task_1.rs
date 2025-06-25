pub fn abs_it(s: &mut [i32])
    requires(
        true
    )
    ensures(
        forall|i: usize| 0 <= i < s.len() ==> if old(s)[i] < 0 then s[i] == -old(s)[i] else s[i] == old(s)[i]
    )
    ensures(
        s.len() == old(s).len()
    )
{
}