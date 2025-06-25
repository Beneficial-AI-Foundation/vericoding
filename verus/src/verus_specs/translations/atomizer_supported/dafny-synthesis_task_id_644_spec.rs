pub fn reverse(a: &mut [i32])
    ensures
        forall|k: usize| 0 <= k < a.len() ==> a[k] == old(a)[(a.len()-1) - k]
{
}

pub fn reverse_upto_k(s: &mut [i32], k: usize)
    requires
        2 <= k <= s.len()
    ensures
        forall|i: usize| 0 <= i < k ==> s[i] == old(s)[k - 1 - i],
        forall|i: usize| k <= i < s.len() ==> s[i] == old(s)[i]
{
}