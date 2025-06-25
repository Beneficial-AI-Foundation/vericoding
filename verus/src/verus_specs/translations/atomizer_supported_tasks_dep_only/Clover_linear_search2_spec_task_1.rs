pub fn linear_search(a: &[i32], e: i32) -> (n: usize)
    requires(exists|i: usize| 0 <= i < a.len() && a[i] == e)
    ensures(|n: usize| 0 <= n < a.len() && a[n] == e)
    ensures(|n: usize| forall|k: usize| 0 <= k < n ==> a[k] != e)
{
}