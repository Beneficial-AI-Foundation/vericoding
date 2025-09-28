// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if a sequence has no duplicate elements
ghost predicate IsUnique(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Helper predicate to check if all elements from source appear in target
ghost predicate AllElementsIn(source: seq<real>, target: seq<real>)
{
    forall x :: x in source ==> x in target
}

// Helper predicate to check if all elements in target come from one of the sources
ghost predicate AllElementsFrom(target: seq<real>, source1: seq<real>, source2: seq<real>)
{
    forall x :: x in target ==> x in source1 || x in source2
}

// Method to compute the union of two sequences, returning sorted unique elements
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Min computes the minimum element of a non-empty sequence */
function Min(s: seq<real>): real
    requires |s| > 0
    decreases |s|
    ensures result in s
    ensures forall x :: x in s ==> result <= x
{
  if |s| == 1 then s[0]
  else let tailMin := Min(s[1..]) in if s[0] < tailMin then s[0] else tailMin
}

/* helper modified by LLM (iteration 5): RemoveAll returns the sequence with all occurrences of v removed and characterizes the set difference */
function RemoveAll(s: seq<real>, v: real): seq<real>
    decreases |s|
    ensures set result == set s - {v}
    ensures forall x :: x in result ==> x != v
{
  if |s| == 0 then []
  else if s[0] == v then RemoveAll(s[1..], v)
  else [s[0]] + RemoveAll(s[1..], v)
}
// </vc-helpers>

// <vc-spec>
method Union1d(ar1: seq<real>, ar2: seq<real>) returns (result: seq<real>)
    ensures IsSorted(result)
    ensures IsUnique(result)
    ensures AllElementsIn(ar1, result)
    ensures AllElementsIn(ar2, result)
    ensures AllElementsFrom(result, ar1, ar2)
    ensures |result| <= |ar1| + |ar2|
    ensures forall s :: (IsSorted(s) && IsUnique(s) && 
                        AllElementsIn(ar1, s) && AllElementsIn(ar2, s) && 
                        AllElementsFrom(s, ar1, ar2)) ==> |result| <= |s|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build sorted unique union by repeatedly extracting the minimum and removing all its occurrences */
  var combined := ar1 + ar2;
  var res: seq<real> := [];
  while |combined| > 0
    invariant IsSorted(res)
    invariant IsUnique(res)
    invariant forall x :: x in res ==> x in ar1 || x in ar2
    invariant set res + set combined == set ar1 + set ar2
    invariant forall r, c :: r in res && c in combined ==> r < c
    decreases |combined|
  {
    var m := Min(combined);
    res := res + [m];
    combined := RemoveAll(combined, m);
  }
  result := res;
}
// </vc-code>
