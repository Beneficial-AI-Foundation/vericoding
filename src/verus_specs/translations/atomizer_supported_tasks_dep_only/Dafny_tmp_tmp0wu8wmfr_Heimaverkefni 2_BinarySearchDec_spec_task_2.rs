pub fn SearchLoop(a: Seq<f64>, i: int, j: int, x: f64) -> (k: int)
    requires(0 <= i <= j <= a.len())
    requires(forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q])
    ensures(|k: int| i <= k <= j)
    ensures(|k: int| forall|r: int| i <= r < k ==> a[r] >= x)
    ensures(|k: int| forall|r: int| k <= r < j ==> a[r] < x)
{
}