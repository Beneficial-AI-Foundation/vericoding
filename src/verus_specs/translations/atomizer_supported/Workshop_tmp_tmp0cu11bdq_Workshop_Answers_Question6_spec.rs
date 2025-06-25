pub fn arrayUpToN(n: int) -> (a: Vec<int>)
    requires(n >= 0)
    ensures(a.len() == n)
    ensures(forall|j: int| 0 < j < n ==> a[j] >= 0)
    ensures(forall|j: int, k: int| 0 <= j <= k < n ==> a[j] <= a[k])
{
}