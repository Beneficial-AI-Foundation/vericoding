// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
function Insert(sorted: seq<int>, key: int): seq<int>
  requires IsSorted(sorted)
  ensures multiset(Insert(sorted, key)) == multiset(sorted) + multiset{key}
  ensures IsSorted(Insert(sorted, key))
  decreases sorted
{
  if |sorted| == 0 then
    [key]
  else if key <= sorted[0] then
    [key] + sorted
  else
    [sorted[0]] + Insert(sorted[1..], key)
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  r := [];
  for i: nat := 0; i < |s|; i := i + 1
    invariant 0 <= i <= |s|
    invariant multiset(r) == multiset(s[..i])
    invariant IsSorted(r)
  {
    r := Insert(r, s[i]);
  }
}
// </vc-code>

