// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The issue was with the loop invariant. The invariant forall j: int :: 0 <= j < i && s[j] in present was incorrect. It should be forall j: int :: 0 <= j < i ==> s[j] in present. This ensures that all elements processed so far are in the present set. */
{
  var present: set<int> := {};
  result := [];

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in present <==> (exists k :: 0 <= k < |result| && result[k] == x)
    invariant forall k: int :: 0 <= k < |result| ==> (exists l: int :: 0 <= l < i && s[l] == result[k])
    invariant forall k: int :: 0 <= k < |result| ==> (forall l: int :: 0 <= l < k ==> result[l] != result[k])
    invariant forall x :: x in present ==> (exists k :: 0 <= k < |s| && s[k] == x)
    invariant forall j: int :: 0 <= j < i ==> s[j] in present
  {
    if !(s[i] in present) {
      result := result + [s[i]];
      present := present + {s[i]};
    }
    i := i + 1;
  }
}
// </vc-code>
