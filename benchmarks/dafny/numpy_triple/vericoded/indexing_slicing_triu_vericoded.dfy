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
  result := [];
  for i := 0 to |m|
    invariant |result| == i
    invariant forall r :: 0 <= r < i ==> |result[r]| == |m[0]|
    invariant forall r, c :: 0 <= r < i && 0 <= c < |m[0]| && r + k <= c ==> result[r][c] == m[r][c]
    invariant forall r, c :: 0 <= r < i && 0 <= c < |m[0]| && r + k > c ==> result[r][c] == 0.0
  {
    var row := [];
    for j := 0 to |m[0]|
      invariant |row| == j
      invariant forall c :: 0 <= c < j && i + k <= c ==> row[c] == m[i][c]
      invariant forall c :: 0 <= c < j && i + k > c ==> row[c] == 0.0
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
