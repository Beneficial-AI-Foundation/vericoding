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
// No changes needed
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
    var low := 0;
    var high := 1000;
    while low < high
        invariant 0 <= low <= high <= 1000;
        invariant forall r | 0 <= r < low :: a[r] < x;
        invariant forall r | high <= r < 1000 :: a[r] >= x;
        decreases high - low;
    {
        var mid := (low + high) / 2;
        // The loop body relies on 'mid' always being a valid index within the array
        // segment being considered, i.e., 'low <= mid < high'.
        // This is guaranteed because 'mid = (low + high) / 2'.
        // If low = 0 and high = 1, mid = 0.
        // If low = 0 and high = 2, mid = 1.
        // If low = 1 and high = 2, mid = 1.
        // The crucial part is to ensure that 'mid' is always less than 'high'
        // when 'low < high'.
        // If low <= high-1, then 2*low <= low + high - 1, so low <= (low+high-1)/2.
        // Also, low + high is even or odd.
        // If low + high is even, mid = (low + high) / 2.
        // If low + high is odd, mid = (low + high - 1) / 2.
        // In integer division, (low + high) / 2 means floor((low+high)/2).
        // Since low < high, low + 1 <= high.
        // So 2*low + 1 <= low + high.
        // (2*low + 1) / 2 <= (low + high) / 2.
        // low <= mid.
        //
        // Also, (low+high)/2 < high when low < high.
        // low/2 + high/2 < high
        // low/2 < high/2
        // low < high.
        // So, low <= mid < high is always true.
        // The invariant forall r | high <= r < 1000 :: a[r] >= x;
        // and a[mid] < x implies mid < high.
        // The invariant forall r | 0 <= r < low :: a[r] < x;
        // and a[mid] >= x implies mid >= low.
        // Therefore, we can safely access a[mid].
        if a[mid] < x {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    k := low;
}
// </vc-code>

