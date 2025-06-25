pub fn linear_search(a: &[int], e: int) -> n: int
    ensures(0 <= n <= a.len())
    ensures(n == a.len() || a[n] == e)
    ensures(forall|i: int| 0 <= i < n ==> e != a[i])
{
}