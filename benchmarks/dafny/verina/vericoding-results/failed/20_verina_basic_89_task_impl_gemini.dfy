// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified proof body */
lemma InImpliesExists(s: seq<int>, x: int)
  requires x in s
  ensures exists i: int :: 0 <= i < |s| && s[i] == x
{
}
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
{
  /* code modified by LLM (iteration 5): added witness to else branch to prove existence */
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    // All elements are unique in the result
    invariant forall k: int, l: int :: 0 <= k < l < |result| ==> result[k] != result[l]
    // Every element in result is in the processed part of s
    invariant forall k: int :: 0 <= k < |result| ==> exists j: int :: 0 <= j < i && s[j] == result[k]
    // Every element in the processed part of s is in result
    invariant forall j: int :: 0 <= j < i ==> exists k: int :: 0 <= k < |result| && result[k] == s[j]
  {
    var x := s[i];
    if x !in result {
      result := result + [x];
    } else {
      var k :| 0 <= k < |result| && result[k] == x;
    }
    i := i + 1;
  }
}
// </vc-code>
