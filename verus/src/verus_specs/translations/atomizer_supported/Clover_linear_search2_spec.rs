pub fn linear_search(a: &[int], e: int) -> (n: int)
    requires(exists|i: int| 0 <= i < a.len() && a[i] == e)
    ensures(|n: int| 0 <= n < a.len() && a[n] == e)
    ensures(|n: int| forall|k: int| 0 <= k < n ==> a[k] != e)
{
}