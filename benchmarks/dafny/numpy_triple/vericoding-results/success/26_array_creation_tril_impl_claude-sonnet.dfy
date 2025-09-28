// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method tril(m: seq<seq<real>>, k: int := 0) returns (result: seq<seq<real>>)
    requires |m| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|  // All rows have same length
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
    // Core property: element-wise specification
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
        result[i][j] == (if i >= j - k then m[i][j] else 0.0)
    // Sanity check: diagonal elements preserved when k = 0
    ensures k == 0 ==> 
        forall idx :: 0 <= idx < |m| && idx < |m[0]| ==>
            result[idx][idx] == m[idx][idx]
    // Sanity check: all elements preserved when k is very large
    ensures k >= |m[0]| as int ==>
        forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
            result[i][j] == m[i][j]
    // Sanity check: all elements zeroed when k is very negative
    ensures k <= -(|m| as int) ==>
        forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
            result[i][j] == 0.0
    // Shape preservation property
    ensures |result| == |m| && 
        (forall i :: 0 <= i < |result| ==> |result[i]| == |m[i]|)
    // Lower triangle preservation: elements satisfying i >= j - k are unchanged
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[i]| && i >= j - k ==>
        result[i][j] == m[i][j]
    // Upper triangle zeroing: elements satisfying i < j - k are set to zero
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[i]| && i < j - k ==>
        result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall idx :: 0 <= idx < i ==> |result[idx]| == |m[0]|
    invariant forall row_idx, col_idx :: 0 <= row_idx < i && 0 <= col_idx < |result[row_idx]| ==>
      result[row_idx][col_idx] == (if row_idx >= col_idx - k then m[row_idx][col_idx] else 0.0)
  {
    var row := [];
    var j := 0;
    while j < |m[i]|
      invariant 0 <= j <= |m[i]|
      invariant |row| == j
      invariant forall col_idx :: 0 <= col_idx < j ==>
        row[col_idx] == (if i >= col_idx - k then m[i][col_idx] else 0.0)
    {
      if i >= j - k {
        row := row + [m[i][j]];
      } else {
        row := row + [0.0];
      }
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
