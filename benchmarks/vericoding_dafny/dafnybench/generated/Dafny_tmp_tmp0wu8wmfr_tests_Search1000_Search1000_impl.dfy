// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

// <vc-helpers>
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
    var lo := 0;
    var hi := 1000;
    
    while lo < hi
        invariant 0 <= lo <= hi <= 1000;
        invariant forall r | 0 <= r < lo :: a[r] < x;
        invariant forall r | hi <= r < 1000 :: a[r] >= x;
    {
        var mid := (lo + hi) / 2;
        if a[mid] < x {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    
    k := lo;
}
// </vc-code>

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