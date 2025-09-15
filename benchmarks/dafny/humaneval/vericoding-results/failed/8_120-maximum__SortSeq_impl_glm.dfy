// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed RemoveElem postcondition to allow duplicates and removed incorrect y != x condition */
function FindMin(s: seq<int>): int
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> FindMin(s) <= s[i]
  ensures FindMin(s) in s
{
  if |s| == 1 then s[0] else min(s[0], FindMin(s[1..]))
}

/* helper modified by LLM (iteration 5): Added decreases clause to RemoveElem to help Dafny prove termination and postconditions */
function RemoveElem(s: seq<int>, x: int): seq<int>
  requires x in s
  decreases s
  ensures |RemoveElem(s, x)| == |s| - 1
  ensures multiset(RemoveElem(s, x)) == multiset(s) - multiset([x])
  ensures forall y :: y in RemoveElem(s, x) ==> y in s
{
  if |s| == 1 then []
  else if s[0] == x then s[1..]
  else [s[0]] + RemoveElem(s[1..], x)
}

function min(a: int, b: int): int
{
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes, but RemoveElem helper was fixed with decreases clause */
{
  var unsorted := s;
  sorted := [];
  
  while |unsorted| > 0
    invariant |sorted| + |unsorted| == |s|
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    invariant forall i :: 0 <= i < |sorted| ==> sorted[i] in s
    invariant forall i :: 0 <= i < |unsorted| ==> unsorted[i] in s
    invariant multiset(sorted) + multiset(unsorted) == multiset(s)
    invariant forall i, j :: 0 <= i < |sorted| && 0 <= j < |unsorted| ==> sorted[i] <= unsorted[j]
  {
    var minElement := FindMin(unsorted);
    sorted := sorted + [minElement];
    unsorted := RemoveElem(unsorted, minElement);
  }
}
// </vc-code>
