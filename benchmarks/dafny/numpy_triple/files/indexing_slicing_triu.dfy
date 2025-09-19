// <vc-preamble>
// Method to extract the upper triangle of a matrix relative to the k-th diagonal
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Triu(m: seq<seq<real>>, k: int) returns (result: seq<seq<real>>)
    // Input matrix must be well-formed (rectangular)
    requires |m| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    
    // Output matrix has same dimensions as input
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
    
    // Elements on and above the k-th diagonal are preserved
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[0]| && i + k <= j ==>
        result[i][j] == m[i][j]
    
    // Elements below the k-th diagonal are zeroed
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[0]| && i + k > j ==>
        result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
