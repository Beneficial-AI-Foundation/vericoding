// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
predicate IsSorted(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if a sequence has no duplicate elements
predicate NoDuplicates(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Main method implementing numpy.setxor1d behavior
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): MinInSeq returns a minimum with proven membership and ordering; RemoveAll and FilterNotIn provide membership and length guarantees; UniqueSortedFromSeq constructs a sorted unique sequence from any sequence */
function MinInSeq(s: seq<real>): real
  requires |s| > 0
  ensures MinInSeq(s) in s
  ensures forall i :: 0 <= i < |s| ==> MinInSeq(s) <= s[i]
  decreases |s|
{
  if |s| == 1 then s[0] else var m := MinInSeq(s[1..]); if s[0] <= m then s[0] else m
}

function RemoveAll(s: seq<real>, v: real): seq<real>
  ensures forall x :: x in RemoveAll(s, v) <==> x in s && x != v
  ensures v !in RemoveAll(s, v)
  ensures |RemoveAll(s, v)| <= |s|
  ensures (v in s) ==> |RemoveAll(s, v)| < |s|
  decreases |s|
{
  if |s| == 0 then [] else if s[0] == v then RemoveAll(s[1..], v) else [s[0]] + RemoveAll(s[1..], v)
}

function FilterNotIn(s: seq<real>, other: seq<real>): seq<real>
  ensures forall x :: x in FilterNotIn(s, other) <==> x in s && x !in other
  ensures |FilterNotIn(s, other)| <= |s|
  decreases |s|
{
  if |s| == 0 then [] else if s[0] in other then FilterNotIn(s[1..], other) else [s[0]] + FilterNotIn(s[1..], other)
}

function UniqueSortedFromSeq(s: seq<real>): seq<real>
  ensures IsSorted(UniqueSortedFromSeq(s))
  ensures NoDuplicates(UniqueSortedFromSeq(s))
  ensures forall x :: x in UniqueSortedFromSeq(s) <==> x in s
  decreases |s|
{
  if |s| == 0 then [] else var m := MinInSeq(s); [m] + UniqueSortedFromSeq(RemoveAll(s, m))
}
// </vc-helpers>

// <vc-spec>
method numpy_setxor1d(ar1: seq<real>, ar2: seq<real>) returns (result: seq<real>)
    // No preconditions required
    ensures IsSorted(result)
    // Result contains no duplicates
    ensures NoDuplicates(result)
    // Every element in result is from exactly one input array
    ensures forall x :: x in result ==> 
        (x in ar1 && x !in ar2) || (x in ar2 && x !in ar1)
    // Every element that appears in exactly one input array is in the result
    ensures forall x :: 
        ((x in ar1 && x !in ar2) || (x in ar2 && x !in ar1)) ==> x in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute symmetric difference by filtering each array and producing a unique sorted concatenation */
  var s1 := FilterNotIn(ar1, ar2);
  var s2 := FilterNotIn(ar2, ar1);
  result := UniqueSortedFromSeq(s1 + s2);
}
// </vc-code>
