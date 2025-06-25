pub fn SearchRecursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires(0 <= i <= j <= a.len())
    ensures(|k: int| i <= k < j || k == -1)
    ensures(|k: int| k != -1 ==> a[k] == x)
    ensures(|k: int| k != -1 ==> forall|r: int| k < r < j ==> a[r] != x)
    ensures(|k: int| k == -1 ==> forall|r: int| i <= r < j ==> a[r] != x)
{
}