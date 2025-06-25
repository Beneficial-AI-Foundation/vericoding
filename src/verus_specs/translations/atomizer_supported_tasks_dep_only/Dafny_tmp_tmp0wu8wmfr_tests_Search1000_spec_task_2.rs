// Is2Pow(n) is true iff n==2^k for some k>=0.
pub open spec fn Is2Pow(n: int) -> bool {
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && Is2Pow(n / 2)
    }
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
pub fn Search2PowLoop(a: &[int], i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < i + n ==> a[p] <= a[q],
        Is2Pow(n + 1),
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k ==> a[r] < x,
        forall|r: int| k <= r < i + n ==> a[r] >= x,
{
}