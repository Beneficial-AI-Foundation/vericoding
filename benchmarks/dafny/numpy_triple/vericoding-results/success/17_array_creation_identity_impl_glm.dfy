// <vc-preamble>
// Type alias to represent floating-point numbers
type Float = real

// Method to create an n×n identity matrix
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Identity(n: nat) returns (result: seq<seq<Float>>)
  // Precondition: n is a valid size for a matrix
  requires n >= 0
  
  // Postconditions: result is an n×n identity matrix
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> |result[i]| == n
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> 
    result[i][j] == (if i == j then 1.0 else 0.0)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := [];
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == n
    invariant forall k, l :: 0 <= k < i && 0 <= l < n ==> result[k][l] == (if k == l then 1.0 else 0.0)
  {
    var row := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == (if i == k then 1.0 else 0.0)
    {
      row := row + [if i == j then 1.0 else 0.0];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
