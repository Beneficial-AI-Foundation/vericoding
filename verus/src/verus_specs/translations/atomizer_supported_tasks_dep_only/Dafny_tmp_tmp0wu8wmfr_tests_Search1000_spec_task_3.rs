pub spec fn Is2Pow(n: int) -> bool {
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && Is2Pow(n / 2)
    }
}

pub fn Search2PowRecursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < i + n ==> a[p as int] <= a[q as int],
        Is2Pow((n + 1) as int),
    ensures
        |k: usize| i <= k <= i + n,
        |k: usize| forall|r: int| i <= r < k ==> a[r] < x,
        |k: usize| forall|r: int| k <= r < i + n ==> a[r] >= x,
{
}