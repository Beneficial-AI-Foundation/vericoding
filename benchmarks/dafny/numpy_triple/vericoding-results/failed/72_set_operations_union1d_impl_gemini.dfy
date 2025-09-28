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
/* helper modified by LLM (iteration 5): added lemma for cardinality of unique sequences */
lemma UniqueSeqCardinality(s: seq<real>)
    requires IsUnique(s)
    ensures |iset(s)| == |s|
{
    if |s| > 0 {
        UniqueSeqCardinality(s[..|s|-1]);
        assert |iset(s[..|s|-1])| == |s[..|s|-1]|;
        assert s[|s|-1] !in s[..|s|-1];
    }
}

method Insert(s: seq<real>, x: real) returns (res: seq<real>)
    requires IsSorted(s) && IsUnique(s)
    ensures IsSorted(res)
    ensures IsUnique(res)
    ensures forall e :: e in res <==> (e in s || e == x)
    ensures x in res
    ensures |res| <= |s| + 1
{
    var i := 0;
    while i < |s| && s[i] < x
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] < x
    {
        i := i + 1;
    }

    if i < |s| && s[i] == x {
        res := s;
    } else {
        res := s[..i] + [x] + s[i..];
    }
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
  /* code modified by LLM (iteration 5): using iset invariant to help prove postconditions */
  var combined := ar1 + ar2;
  var res_so_far: seq<real> := [];
  var i := 0;
  while i < |combined|
    invariant IsSorted(res_so_far)
    invariant IsUnique(res_so_far)
    invariant 0 <= i <= |combined|
    invariant iset(res_so_far) == iset(combined[..i])
  {
    res_so_far := Insert(res_so_far, combined[i]);
    i := i + 1;
  }
  result := res_so_far;
}
// </vc-code>
