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
lemma Is2PowPositive(n: int)
  requires Is2Pow(n)
  ensures n >= 1
{
  if n < 1 {
    assert !Is2Pow(n);
  }
}

lemma Is2PowHalf(n: int)
  requires n > 1
  requires Is2Pow(n)
  ensures Is2Pow(n/2)
{
  assert n%2 == 0;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var low := i;
  var high := i + n;
  var mid: int;
  var m := n + 1;
  while m > 1
    decreases m
    invariant 0 <= low <= high <= a.Length
    invariant m >= 1
    invariant Is2Pow(m)
    invariant high - low == m - 1
    invariant low >= i
    invariant high <= i + n
    invariant forall r | i <= r < low :: a[r] < x
    invariant forall r | high <= r < i + n :: a[r] >= x
  {
    m := m / 2;
    mid := low + m - 1;
    assert mid < high;
    if a[mid] < x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  return low;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.