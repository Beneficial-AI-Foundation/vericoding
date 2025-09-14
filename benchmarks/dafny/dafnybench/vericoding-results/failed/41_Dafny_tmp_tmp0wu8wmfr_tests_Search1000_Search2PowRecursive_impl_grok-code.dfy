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

lemma Is2Pow_sub(n: int)
    requires Is2Pow(n+1) && n > 0
    ensures exists k: int :: k >= 0 && n+1 == power(2, k) && Is2Pow(1 + (n-1)/2) && Is2Pow(1 + n - (n-1)/2 - 1)
{}
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
    var half := (n-1) / 2;
    var mid := i + half;
    var left_n := half;
    var right_i := mid + 1;
    var right_n := n - half - 1;
    Is2Pow_sub(n);
    if a[mid] >= x {
      k := Search2PowRecursive(a, i, left_n, x);
    } else {
      k := Search2PowRecursive(a, right_i, right_n, x);
    }
  }
}
// </vc-code>

