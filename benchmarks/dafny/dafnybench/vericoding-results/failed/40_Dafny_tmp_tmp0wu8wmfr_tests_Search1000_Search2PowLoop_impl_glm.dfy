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

// <vc-helpers>
predicate WellFormed(lo: int, hi: int) {
    Is2Pow(hi - lo + 2)
}

lemma WellFormedMid(lo: int, hi: int)
    requires WellFormed(lo, hi)
    requires lo <= hi
    ensures WellFormed(lo, (lo + hi) / 2)
    ensures WellFormed((lo + hi) / 2 + 1, hi)
{
    var mid := (lo + hi) / 2;
    calc {
        hi - lo + 2;
        { 
            assert hi - mid == mid - lo || hi - mid == mid - lo + 1;
            hi - mid + mid - lo + 2;
        }
        (hi - mid) + (mid - lo + 1) + 1;
        { 
            assert hi - mid + 1 == (mid - lo + 1) || hi - mid + 1 == (mid - lo + 1) + 1;
        }
    }
    if (hi - mid) == (mid - lo) {
        assert Is2Pow(hi - mid + 1);
        assert Is2Pow(mid - lo + 2);
    } else {
        assert hi - mid + 1 == 2 * (mid - lo + 1);
        assert Is2Pow((hi - mid + 1) / 2);
        assert Is2Pow(mid - lo + 2);
    }
}

lemma WellFormedStep(lo: int, hi: int, x: int, a: array<int>, mid: int)
    requires WellFormed(lo, hi)
    requires lo <= hi
    requires mid == (lo + hi) / 2
    ensures a[mid] < x ==> WellFormed(mid + 1, hi)
    ensures a[mid] >= x ==> WellFormed(lo, mid - 1)
{
    WellFormedMid(lo, hi);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
var lo := i;
var hi := i + n - 1;
while lo <= hi
    invariant i <= lo <= hi + 1
    invariant WellFormed(lo, hi)
    invariant forall r | i <= r < lo :: a[r] < x
    invariant forall r | hi < r < i + n :: a[r] >= x
{
    var mid := (lo + hi) / 2;
    if a[mid] < x {
        WellFormedStep(lo, hi, x, a, mid);
        lo := mid + 1;
    } else {
        WellFormedStep(lo, hi, x, a, mid);
        hi := mid - 1;
    }
}
k := lo;
// </vc-code>
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.