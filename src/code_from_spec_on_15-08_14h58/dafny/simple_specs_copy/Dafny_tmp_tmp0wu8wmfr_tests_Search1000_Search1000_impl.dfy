//IMPL 
// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM. Surprisingly Dafny needs no help
// to verify the function.
method Search1000( a: array<int>, x: int ) returns ( k: int )
  requires a.Length >= 1000
  requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q]
  ensures 0 <= k <= 1000
  ensures forall r | 0 <= r < k :: a[r] < x
  ensures forall r | k <= r < 1000 :: a[r] >= x
{
  var low := 0;
  var high := 1000;
  
  while low < high
    invariant 0 <= low <= high <= 1000
    invariant forall r | 0 <= r < low :: a[r] < x
    invariant forall r | high <= r < 1000 :: a[r] >= x
  {
    var mid := (low + high) / 2;
    if a[mid] < x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  k := low;
}