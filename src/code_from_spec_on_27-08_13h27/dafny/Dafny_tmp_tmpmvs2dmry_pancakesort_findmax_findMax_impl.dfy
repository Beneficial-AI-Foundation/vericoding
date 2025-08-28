// returns an index of the largest element of array 'a' in the range [0..n)

// <vc-helpers>
// Helper lemma to ensure array content remains unchanged
lemma ArrayContentUnchanged(a: array<int>, oldA: seq<int>)
  ensures multiset(a[..]) == multiset(oldA)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// </vc-spec>

// <vc-code>
method findMax(a: array<int>, n: int) returns (r: int)
  requires a.Length > 0
  requires 0 < n <= a.Length
  ensures 0 <= r < n <= a.Length
  ensures forall k :: 0 <= k < n ==> a[r] >= a[k]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var maxIndex := 0;
  var i := 1;
  var oldA := a[..];
  
  while i < n
    invariant 0 <= maxIndex < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[maxIndex] >= a[k]
    invariant multiset(a[..]) == multiset(oldA)
  {
    if a[i] > a[maxIndex] {
      maxIndex := i;
    }
    i := i + 1;
  }
  
  r := maxIndex;
}
// </vc-code>
