// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
function Insert(x: int, t: seq<int>): seq<int>
  ensures multiset(Insert(x, t)) == multiset(t) + multiset([x])
  ensures IsSorted(t) ==> IsSorted(Insert(x, t))
  decreases |t|
{
  if |t| == 0 then
    [x]
  else if x <= t[0] then
    [x] + t
  else
    [t[0]] + Insert(x, t[1..])
}

function Sort(s: seq<int>): seq<int>
  ensures multiset(Sort(s)) == multiset(s)
  ensures IsSorted(Sort(s))
  decreases |s|
{
  if |s| == 0 then
    []
  else
    Insert(s[0], Sort(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  r := Sort(s);
}
// </vc-code>

