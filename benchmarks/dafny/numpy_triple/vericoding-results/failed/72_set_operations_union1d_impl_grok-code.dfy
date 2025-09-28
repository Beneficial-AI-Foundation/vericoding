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
/* helper modified by LLM (iteration 5): Fixed loop bound to prevent index out of range and added ensures for element preservation */
method Sort(s: seq<real>) returns (result: seq<real>)
  ensures IsSorted(result)
  ensures IsUnique(result)
  ensures AllElementsIn(s, result)
{
  result := [];
  for i := 0 to |s|-1
  {
    var elem := s[i];
    var j := 0;
    while j < |result| && result[j] < elem
    {
      j := j + 1;
    }
    // Only add if not already present to ensure uniqueness
    if j == |result| || result[j] != elem {
      result := result[..j] + [elem] + result[j..];
    }
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
/* code modified by LLM (iteration 5): Appended sequences and sorted to compute union while ensuring uniqueness */
{
  var temp := ar1 + ar2;
  result := Sort(temp);
}
// </vc-code>
