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
/* code modified by LLM (iteration 5): Fixed duplicate variable declaration by removing var keyword */
{
  result := [];
  for i := 0 to |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall p :: 0 <= p < i ==> |result[p]| == |m[0]|
    invariant forall p, j' :: 0 <= p < i && 0 <= j' < |m[0]| && p + k <= j' ==> result[p][j'] == m[p][j']
    invariant forall p, j' :: 0 <= p < i && 0 <= j' < |m[0]| && p + k > j' ==> result[p][j'] == 0.0
  {
    var row := [];
    for j := 0 to |m[0]|
      invariant 0 <= j <= |m[0]|
      invariant |row| == j
      invariant forall q :: 0 <= q < j && i + k <= q ==> row[q] == m[i][q]
      invariant forall q :: 0 <= q < j && i + k > q ==> row[q] == 0.0
    {
      if i + k <= j {
        row := row + [m[i][j]];
      } else {
        row := row + [0.0];
      }
    }
    result := result + [row];
  }
}
// </vc-code>
