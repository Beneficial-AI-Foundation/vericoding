// <vc-preamble>
// Type alias to represent floating-point numbers
type Float = real

// Method to create an n×n identity matrix
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == n
    invariant forall k, j :: 0 <= k < i && 0 <= j < n ==> result[k][j] == (if k == j then 1.0 else 0.0)
  {
    var row := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == (if i == k then 1.0 else 0.0)
    {
      if i == j {
        row := row + [1.0];
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
