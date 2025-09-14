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
lemma {:induction false} Pow2Div2Lemma(n: int)
  requires Is2Pow(n+1)
  requires n >= 1
  ensures (n/2) + 1 == (n+1)/2
{
  if n > 1 {
    // n+1 is power of 2, so n is odd
    assert n % 2 == 1;
    Pow2Div2Lemma((n-1)/2);
  }
}

lemma Pow2TerminationLemma(n: int)
  requires Is2Pow(n+1)
  requires 1 <= k <= n
  ensures Is2Pow((k-1)+1) || Is2Pow(k+1)
{
  // This helps establish that when we split the array of size 2^m-1,
  // the two halves also have the power-of-two-minus-one property
}
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
{
    var low := i;
    var high := i + n;
    var size := n;
    
    while low < high
        invariant i <= low <= high <= i+n
        invariant size == high - low
        invariant Is2Pow(size+1)
        invariant forall r | i <= r < low :: a[r] < x
        invariant forall r | high <= r < i+n :: a[r] >= x
        decreases size
    {
        var mid := (low + high) / 2;
        if a[mid] < x {
            low := mid + 1;
            size := high - low;
            // Prove that new size still has Is2Pow property
            assert Is2Pow(size+1);
        } else {
            high := mid;
            size := high - low;
            // Prove that new size still has Is2Pow property  
            assert Is2Pow(size+1);
        }
    }
    
    k := low;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.