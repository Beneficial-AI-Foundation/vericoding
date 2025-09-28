// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper effectively checks if a matrix is a broadcast of a vector, meaning each row of the matrix is identical to the given vector, and the matrix has 'm' rows. */
predicate IsBroadcastOf(matrix: seq<seq<real>>, vector: seq<real>, m: nat)
  requires m > 0
  requires |vector| > 0
{
  (|matrix| == m &&
   (forall i :: 0 <= i < m ==> |matrix[i]| == |vector|) &&
   (forall i :: 0 <= i < m ==> matrix[i] == vector))
}
// </vc-helpers>

// <vc-spec>
method BroadcastTo(v: seq<real>, m: nat) returns (result: seq<seq<real>>)
  requires |v| > 0  // Input vector must be non-empty
  requires m > 0    // Target number of rows must be positive
  ensures |result| == m  // Result has exactly m rows
  ensures forall i :: 0 <= i < m ==> |result[i]| == |v|  // Each row has same length as input
  // Primary property: each element (i,j) equals v[j]
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> result[i][j] == v[j]
  // Row identity: each row is exactly the input vector  
  ensures forall i :: 0 <= i < m ==> result[i] == v
  // Column uniformity: each column contains a single repeated value
  ensures forall j, i1, i2 :: 0 <= j < |v| && 0 <= i1 < m && 0 <= i2 < m ==> result[i1][j] == result[i2][j]
  // Value preservation: no new values are introduced, each element comes from original vector
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j
  // Broadcast invariant: all rows are identical
  ensures forall i1, i2 :: 0 <= i1 < m && 0 <= i2 < m ==> result[i1] == result[i2]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous implementation had a direct construction for result variable `result := seq(m, i => v);` but the postcondition `ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j` could not be verified automatically. To fix this, an explicit loop has been added. Within the loop, a new row `current_row` is created using the sequence constructor from each element of `v`. Each `current_row` is then appended to form the `result` sequence of sequences. This explicit construction assists the verifier by making the relationship between `result[i][j]` and `v[j]` clear through the direct assignment. */
{
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall x :: 0 <= x < i ==> result[x] == v
    decreases m - i
  {
    var current_row := seq(|v|, j => v[j]);
    result := result + [current_row];
    i := i + 1;
  }
}
// </vc-code>
