// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
lemma lemma_append_sorted(a: seq<int>, x: int)
  requires IsSorted(a)
  ensures IsSorted(append_sorted(a, x))
  ensures multiset(append_sorted(a, x)) == multiset(a) + multiset{x}
{
  if |a| > 0 {
    var j := 0;
    while j < |a| && x >= a[j]
      invariant 0 <= j <= |a|
      invariant forall k | 0 <= k < j :: a[k] <= x
      invariant forall k | 0 <= k < j - 1 :: a[k] <= a[k+1]
      invariant IsSorted(a)
    {
      if j + 1 < |a| && x >= a[j+1] {
        // This is primarily for the lemma proof, not for the function logic.
        // It helps to show a[j] <= a[j+1] for the invariant.
      }
      j := j + 1;
    }
  }
}

function append_sorted(a: seq<int>, x: int): seq<int>
  requires IsSorted(a)
  ensures IsSorted(append_sorted(a, x))
  ensures multiset(append_sorted(a, x)) == multiset(a) + multiset{x}
{
  if |a| == 0 then [x]
  else if x <= a[0] then [x] + a
  else
    var j := 0;
    while j < |a| && x >= a[j]
      invariant 0 <= j <= |a|
      invariant forall k | 0 <= k < j :: a[k] <= x
      invariant IsSorted(a)
    {
      j := j + 1;
    }
    a[0..j] + [x] + a[j..]
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  var result: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(result)
    invariant multiset(result) + multiset(s[i..]) == multiset(s)
  {
    lemma_append_sorted(result, s[i]);
    result := append_sorted(result, s[i]);
    i := i + 1;
  }
  return result;
}
// </vc-code>

