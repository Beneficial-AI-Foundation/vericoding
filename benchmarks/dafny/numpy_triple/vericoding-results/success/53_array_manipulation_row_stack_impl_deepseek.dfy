// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
  function maxLength(arrays: seq<seq<real>>): int
    requires |arrays| > 0
  {
    |arrays[0]|
  }

  predicate AllSameLength(arrays: seq<seq<real>>)
    requires |arrays| > 0
  {
    forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|
  }

  lemma ArrayPreservationLemma(arrays: seq<seq<real>>, result: seq<seq<real>>)
    requires |arrays| > 0
    requires AllSameLength(arrays)
    requires result == arrays
    ensures |result| == |arrays|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |arrays[0]|
    ensures forall i, j :: 0 <= i < |arrays| && 0 <= j < |arrays[i]| ==> 
      result[i][j] == arrays[i][j]
  {
  }
// </vc-helpers>

// <vc-spec>
method RowStack(arrays: seq<seq<real>>) returns (result: seq<seq<real>>)
  // All input vectors must have the same length
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|
  
  // Result has same number of rows as input arrays
  ensures |result| == |arrays|
  
  // Each row in result has same length as input vectors
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |arrays[0]|
  
  // Each element is preserved: result[i][j] == arrays[i][j]
  ensures forall i, j :: 0 <= i < |arrays| && 0 <= j < |arrays[i]| ==> 
    result[i][j] == arrays[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Direct assignment preserves all properties */
  result := arrays;
}
// </vc-code>
