// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
function InsertSeq(s: seq<int>, x: int): seq<int>
  requires IsSorted(s)
  ensures IsSorted(InsertSeq(s,x))
  ensures multiset(InsertSeq(s,x)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 then [x]
  else if s[0] <= x then [s[0]] + InsertSeq(s[1..], x)
  else [x] + s
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  var t: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant IsSorted(t);
    invariant multiset(t) == multiset(s[..i]);
    decreases |s| - i
  {
    t := InsertSeq(t, s[i]);
    i := i + 1;
  }
  r := t;
}
// </vc-code>

