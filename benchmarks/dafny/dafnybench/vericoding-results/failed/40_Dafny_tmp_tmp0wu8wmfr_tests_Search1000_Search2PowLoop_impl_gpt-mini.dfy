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
lemma Is2PowShrink(len: int)
  requires Is2Pow(len + 1)
  requires len + 1 > 1
  ensures Is2Pow((len + 1) / 2)
{
  if len + 1 > 1 {
    assert (len + 1) % 2 == 0;
    assert Is2Pow((len + 1) / 2);
  }
}

lemma ExtendLeft(a: array<int>, i: int, n: int, lo: int, mid: int, x: int)
  requires 0 <= i <= i + n <= a.Length
  requires i <= lo <= mid < i + n
  requires forall p,q | i <= p < q < i + n :: a[p] <= a[q]
  requires forall r | i <= r < lo :: a[r] < x
  requires a[mid] < x
  ensures forall r | i <= r < mid + 1 :: a[r] < x
{
  // For any r with i <= r < mid we have a[r] <= a[mid] by sortedness,
  // and a[mid] < x, hence a[r] < x. For r == mid we have a[mid] < x.
  assert forall r | i <= r < mid :: a[r] <= a[mid];
  assert forall r | i <= r < mid :: a[r] < x;
  assert a[mid] < x;
  assert forall r | i <= r < mid + 1 :: a[r] < x;
}

lemma ExtendRight(a: array<int>, i: int, n: int, mid: int, hi: int, x: int)
  requires 0 <= i <= i + n <= a.Length
  requires i <= mid < hi <= i + n
  requires forall p,q | i <= p < q < i + n :: a[p] <= a[q]
  requires forall r | hi <= r < i + n :: a[r] >= x
  requires a[mid] >= x
  ensures forall r | mid <= r < i + n :: a[r] >= x
{
  // For any r with mid < r < i+n we have a[mid] <= a[r] by sortedness,
  // and a[mid] >= x, hence a[r] >= x. For r == mid we have a[mid] >= x.
  assert forall r | mid < r < i + n :: a[mid] <= a[r];
  assert forall r | mid < r < i + n :: a[r] >= x;
  assert a[mid] >= x;
  assert forall r | mid <= r < i + n :: a[r] >= x;
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
  var lo := i;
  var hi := i + n;
  while hi - lo > 0
    invariant i <= lo <= hi <= i + n
    invariant forall r | i <= r < lo :: a[r] < x
    invariant forall r | hi <= r < i + n :: a[r] >= x
    invariant Is2Pow(hi - lo + 1)
    decreases hi - lo
  {
    var len := hi - lo;
    var half := (len + 1) / 2;
    var mid := lo + half - 1;
    if a[mid] < x {
      ExtendLeft(a, i, n, lo, mid, x);
      lo := mid + 1;
      Is2PowShrink(len);
    } else {
      ExtendRight(a, i, n, mid, hi, x);
      hi := mid;
      Is2PowShrink(len);
    }
  }
  k := lo;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.