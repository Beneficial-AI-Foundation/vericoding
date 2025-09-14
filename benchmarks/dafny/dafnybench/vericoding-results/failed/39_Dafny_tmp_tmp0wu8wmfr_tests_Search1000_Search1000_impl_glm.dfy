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
predicate Is2Pow( n: int )
    decreases n
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

predicate IsSegSorted(a: array<int>, lo: int, hi: int)
    reads a
    requires 0 <= lo <= hi <= a.Length
{
    forall p,q | lo <= p < q < hi :: a[p] <= a[q]
}

lemma LemmaSplit(a: array<int>, lo: int, hi: int, mid: int)
    requires 0 <= lo <= mid < hi <= a.Length
    requires IsSegSorted(a, lo, hi)
    ensures IsSegSorted(a, lo, mid) && IsSegSorted(a, mid, hi)
{
    // Proof automatically completed by Dafny
}

predicate Search1000ValidRec(a: array<int>, x: int, lo: int, hi: int, k: int)
    reads a
    requires 0 <= lo <= k <= hi <= a.Length
{
    0 <= lo <= k <= hi <= 1000 &&
    (forall r | lo <= r < k :: a[r] < x) &&
    (forall r | k <= r < hi :: a[r] >= x)
}

method Search1000Rec(a: array<int>, x: int, lo: int, hi: int) returns (k: int)
    requires 0 <= lo < hi <= 1000
    requires hi <= a.Length
    requires IsSegSorted(a, lo, hi)
    decreases hi - lo
    ensures Search1000ValidRec(a, x, lo, hi, k)
{
    if lo + 1 == hi {
        if a[lo] < x {
            k := hi;
        } else {
            k := lo;
        }
    } else {
        var mid := (lo + hi) / 2;
        assert mid == lo + (hi - lo) / 2;
        assert lo < mid < hi;
        
        LemmaSplit(a, lo, hi, mid);
        
        if a[mid] < x {
            k := Search1000Rec(a, x, mid + 1, hi);
            assert Search1000ValidRec(a, x, mid + 1, hi, k);
        } else {
            k := Search1000Rec(a, x, lo, mid);
            assert Search1000ValidRec(a, x, lo, mid, k);
        }
    }
}

lemma LemmaRecValidToGlobal(a: array<int>, x: int, k: int)
    requires Search1000ValidRec(a, x, 0, 1000, k)
    ensures 0 <= k <= 1000
    ensures forall r | 0 <= r < k :: a[r] < x
    ensures forall r | k <= r < 1000 :: a[r] >= x
{
    // Follows directly from the predicate definition
}
// </vc-helpers>

// <vc-spec>
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
    k := Search1000Rec(a, x, 0, 1000);
}
// </vc-code>

