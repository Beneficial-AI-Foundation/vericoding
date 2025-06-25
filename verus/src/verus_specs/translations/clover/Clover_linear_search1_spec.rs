pub fn linear_search(a: &[i32], e: i32) -> n: usize
    ensures(n <= a.len())
    ensures(n == a.len() || a[n as int] == e)
    ensures(forall|i: int| 0 <= i < n ==> e != a[i])
{
}