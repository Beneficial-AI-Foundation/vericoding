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
  result := [];
  var i := 0;
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall idx :: 0 <= idx < i ==> |result[idx]| == |m[0]|
    invariant forall idx, j :: 0 <= idx < i && 0 <= j < |result[idx]| ==>
      result[idx][j] == (if idx > j - k then 0.0 else m[idx][j])
  {
    var row := [];
    var j := 0;
    while j < |m[0]|
      invariant 0 <= j <= |m[0]|
      invariant |row| == j
      invariant forall col :: 0 <= col < j ==>
        row[col] == (if i > col - k then 0.0 else m[i][col])
    {
      if i > j - k {
        row := row + [0.0];
      } else {
        row := row + [m[i][j]];
      }
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
