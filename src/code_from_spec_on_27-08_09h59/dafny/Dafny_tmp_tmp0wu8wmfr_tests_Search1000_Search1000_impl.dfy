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
lemma BinarySearchInvariant(a: array<int>, x: int, left: int, right: int, k: int)
    requires a.Length >= 1000
    requires 0 <= left <= right <= 1000
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q]
    requires forall r | 0 <= r < left :: a[r] < x
    requires forall r | right <= r < 1000 :: a[r] >= x
    requires left <= k <= right
    requires (k == left && (k >= 1000 || a[k] >= x)) || (k > left && k-1 < a.Length && a[k-1] < x && (k >= 1000 || (k < a.Length && a[k] >= x)))
    ensures 0 <= k <= 1000
    ensures forall r | 0 <= r < k :: r < a.Length ==> a[r] < x
    ensures forall r | k <= r < 1000 :: r < a.Length ==> a[r] >= x
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var left := 0;
    var right := 1000;
    
    while left < right
        invariant 0 <= left <= right <= 1000
        invariant forall r | 0 <= r < left :: a[r] < x
        invariant forall r | right <= r < 1000 :: a[r] >= x
        decreases right - left
    {
        var mid := (left + right) / 2;
        
        if a[mid] < x {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    k := left;
}
// </vc-code>
