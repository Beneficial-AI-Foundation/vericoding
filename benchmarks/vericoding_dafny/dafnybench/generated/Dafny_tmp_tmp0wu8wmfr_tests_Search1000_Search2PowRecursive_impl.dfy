// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
lemma Is2PowHalf(n: int)
    requires n > 0 && Is2Pow(n+1)
    ensures Is2Pow(n/2 + 1)
{
    if n == 0 {
        // This case won't happen due to precondition n > 0
    } else {
        // Since Is2Pow(n+1) and n > 0, we have n+1 >= 2
        // So n+1 = 2^k for some k >= 1
        // This means n+1 is even, so n is odd
        // Therefore n/2 = (n-1)/2 and n/2 + 1 = (n+1)/2
        // Since n+1 = 2^k, we have (n+1)/2 = 2^(k-1)
        // So Is2Pow(n/2 + 1) = Is2Pow(2^(k-1)) = true
    }
}
// </vc-helpers>

// <vc-spec>
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    decreases n;
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        k := i;
    } else {
        var mid := i + n/2;
        Is2PowHalf(n);
        if a[mid] < x {
            k := Search2PowRecursive(a, mid+1, n/2, x);
        } else {
            k := Search2PowRecursive(a, i, n/2, x);
        }
    }
}
// </vc-code>