pub fn Search1000(a: &[i32], x: i32) -> k: i32
    requires(a.len() >= 1000)
    requires(forall|p: usize, q: usize| 0 <= p < q < 1000 ==> a[p] <= a[q])
    ensures(0 <= k <= 1000)
    ensures(forall|r: usize| 0 <= r < k ==> a[r] < x)
    ensures(forall|r: usize| k <= r < 1000 ==> a[r] >= x)
{
}