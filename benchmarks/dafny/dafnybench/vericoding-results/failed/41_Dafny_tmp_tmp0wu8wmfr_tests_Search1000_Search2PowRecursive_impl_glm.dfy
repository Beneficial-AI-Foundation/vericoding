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
lemma Is2PowPlus1(n: int)
    requires 0 < n;
    requires Is2Pow(n);
    ensures Is2Pow(n+1) == false;
{
    if n == 1 {
        
    } else {
        calc {
            n+1;
        ==  { assert n/2 > 0; }
            2*(n/2) + 1;
        }
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
        return i;
    }
    var p := i + n/2;
    assert n/2 > 0;
    assert n-1-n/2 == n/2;
    assert Is2Pow(n/2+1);
    if x < a[p] {
        var m := n/2;
        assert m > 0;
        assert Is2Pow(m+1);
        return Search2PowRecursive(a, i, m, x);
    } else {
        var m := n-1-n/2;
        assert m >= 0;
        assert Is2Pow(m+1);
        return Search2PowRecursive(a, p+1, m, x);
    }
}
// </vc-code>

