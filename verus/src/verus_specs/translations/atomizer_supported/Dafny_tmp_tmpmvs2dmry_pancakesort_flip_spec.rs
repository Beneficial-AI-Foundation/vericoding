pub fn flip(a: &mut [i32], num: usize)
    requires(
        a.len() > 0,
        num < a.len(),
    )
    ensures(
        forall|k: usize| (k <= num) ==> a[k as int] == old(a)[(num - k) as int],
        forall|k: usize| (num < k && k < a.len()) ==> a[k as int] == old(a)[k as int],
    )
{
}