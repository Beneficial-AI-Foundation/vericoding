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
lemma Is2PowDivision(n: int)
    requires n > 1 && Is2Pow(n)
    ensures Is2Pow((n-1)/2 + 1)
    decreases n
{
    if n == 2 {
        assert (n-1)/2 + 1 == 1;
        assert Is2Pow(1);
    } else {
        assert n % 2 == 0;
        assert Is2Pow(n/2);
        assert (n-1)/2 == n/2 - 1;
        assert (n-1)/2 + 1 == n/2;
        assert Is2Pow(n/2);
    }
}

lemma ArrayBounds(a: array<int>, i: int, n: int)
    requires 0 <= i <= i+n <= a.Length
    requires n >= 1
    ensures n >= 1 ==> 0 <= i + (n-1)/2 < a.Length
    ensures n >= 1 ==> 0 <= i <= i + (n-1)/2 <= a.Length
    ensures n >= 1 ==> 0 <= i + (n-1)/2 + 1 <= i + (n-1)/2 + 1 + (n-1)/2 <= a.Length
{
    if n >= 1 {
        var mid := i + (n-1)/2;
        assert mid < i + n;
        assert mid + 1 + (n-1)/2 <= i + n;
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
    if n == 1 {
        if a[i] < x {
            k := i + 1;
        } else {
            k := i;
        }
    } else {
        ArrayBounds(a, i, n);
        var mid := i + (n-1)/2;
        if n > 1 {
            Is2PowDivision(n+1);
        }
        if a[mid] < x {
            k := Search2PowRecursive(a, mid + 1, (n-1)/2, x);
        } else {
            k := Search2PowRecursive(a, i, (n-1)/2, x);
        }
    }
}
// </vc-code>

