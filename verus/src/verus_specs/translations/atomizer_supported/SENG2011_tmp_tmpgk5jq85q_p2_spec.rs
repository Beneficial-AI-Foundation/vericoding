pub fn abs_it(s: &mut [i32])
    requires(true)
    ensures(
        forall|x: usize| 0 <= x < s.len() ==> old(s)[x] < 0 ==> s[x] == -old(s)[x]
    )
    ensures(
        forall|x: usize| 0 <= x < s.len() ==> old(s)[x] >= 0 ==> s[x] == old(s)[x]
    )
{
}