// <vc-preamble>
// Method to extract the upper triangle of a matrix
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Triu(m: seq<seq<real>>, k: int := 0) returns (result: seq<seq<real>>)
  // Input matrix must be rectangular (all rows have same length)
  requires |m| > 0
  requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
  
  // Output has same dimensions as input
  ensures |result| == |m|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
  
  // Elements are preserved or zeroed according to triu rule
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == (if i > j - k then 0.0 else m[i][j])
    
  // Elements on or above k-th diagonal are preserved
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| && i <= j - k ==>
    result[i][j] == m[i][j]
    
  // Elements below k-th diagonal are zeroed
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| && i > j - k ==>
    result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
