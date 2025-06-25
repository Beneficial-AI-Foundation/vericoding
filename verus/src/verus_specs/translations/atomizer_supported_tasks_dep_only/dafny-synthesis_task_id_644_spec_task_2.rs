pub fn reverse_upto_k(s: &mut [i32], k: usize)
    requires(
        2 <= k <= s.len()
    )
    ensures(
        forall|i: usize| 0 <= i < k ==> s[i] == old(s)[k - 1 - i]
    )
    ensures(
        forall|i: usize| k <= i < s.len() ==> s[i] == old(s)[i]
    )
{
}