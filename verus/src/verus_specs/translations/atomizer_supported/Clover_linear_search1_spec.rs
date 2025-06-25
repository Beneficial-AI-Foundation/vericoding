pub fn linear_search(a: &[i32], e: i32) -> n: usize
    ensures([
        n <= a.len(),
        n == a.len() || a[n as int] == e,
        forall|i: int| 0 <= i < n ==> e != a[i],
    ])
{
}