// <vc-preamble>
// Method to compute the scaled companion matrix of Legendre series coefficients
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified helper function for companion matrix element */
function companionElement(i: int, j: int): real
  requires i >= 0 && j >= 0
{
  if (i == j + 1 || j == i + 1) then
    var minIdx := if i < j then i else j;
    ((i + 1) * (j + 1)) as real / ((2.0 * minIdx as real + 1.0) * (2.0 * minIdx as real + 3.0))
  else
    0.0
}
// </vc-helpers>

// <vc-spec>
method legcompanion(c: seq<real>) returns (result: seq<seq<real>>)
  // Input must have at least 2 coefficients to form a meaningful companion matrix
  requires |c| >= 2
  // The leading coefficient (last element) must be non-zero for well-defined companion matrix
  requires c[|c|-1] != 0.0
  
  // The result is a square matrix of dimension (|c|-1) x (|c|-1)
  ensures |result| == |c| - 1
  // Each row has the correct length to form a square matrix
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |c| - 1
  // The companion matrix is symmetric: result[i][j] == result[j][i]
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| ==> result[i][j] == result[j][i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed symmetry invariant by setting both mat[i,j] and mat[j,i] simultaneously */
  var n := |c| - 1;
  var mat := new real[n, n];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> mat[ii, jj] == mat[jj, ii]
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> mat[ii, jj] == mat[jj, ii]
      invariant forall jj :: 0 <= jj < j ==> mat[i, jj] == mat[jj, i]
    {
      var element := companionElement(i, j);
      mat[i, j] := element;
      mat[j, i] := element;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := [];
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> result[ii][jj] == mat[ii, jj]
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < i ==> result[ii][jj] == result[jj][ii]
  {
    var row := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> row[jj] == mat[i, jj]
    {
      row := row + [mat[i, j]];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
