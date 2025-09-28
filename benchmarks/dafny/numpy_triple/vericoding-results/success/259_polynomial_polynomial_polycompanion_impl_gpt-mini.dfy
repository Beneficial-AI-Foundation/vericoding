// <vc-preamble>
// Method to construct the companion matrix of a polynomial
// Given coefficients c = [c0, c1, ..., cn, c_{n+1}] representing polynomial
// p(x) = c0 + c1*x + ... + c_{n+1}*x^{n+1}, returns the (n+1)×(n+1) companion matrix
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): row entry selector for companion matrix */
function rowEntry(c: seq<real>, i: int, j: int): real
  requires |c| >= 2
  requires 0 <= i < |c| - 1
  requires 0 <= j < |c| - 1
  requires c[|c| - 1] != 0.0
{
  if i < |c| - 2 then
    (if j == i + 1 then 1.0 else 0.0)
  else
    (if j < |c| - 2 then -c[j] / c[|c| - 1] else 0.0)
}
// </vc-helpers>

// <vc-spec>
method PolyCompanion(c: seq<real>) returns (matrix: seq<seq<real>>)
    requires |c| >= 2  // Need at least 2 coefficients
    requires c[|c|-1] != 0.0  // Leading coefficient must be non-zero
    ensures |matrix| == |c| - 1  // Matrix is (n+1)×(n+1) for degree n+1 polynomial
    ensures forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |c| - 1  // Square matrix
    ensures forall i, j :: 0 <= i < |matrix| - 1 && 0 <= j < |matrix[i]| ==>
        // First n rows: shifted identity pattern (1 in position i+1, 0 elsewhere)
        (matrix[i][j] == (if j == i + 1 then 1.0 else 0.0))
    ensures forall j :: 0 <= j < |matrix| - 1 ==>
        // Last row: normalized negative coefficients
        matrix[|matrix| - 1][j] == -c[j] / c[|c| - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build companion matrix using rowEntry with invariants */
  var m := |c| - 1;
  matrix := [];
  var i := 0;
  while i < m
    decreases m - i
    invariant 0 <= i <= m
    invariant |matrix| == i
    invariant forall k :: 0 <= k < i ==> |matrix[k]| == m
    invariant forall k, j :: 0 <= k < i && 0 <= j < m ==> matrix[k][j] == rowEntry(c, k, j)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < m
      decreases m - j
      invariant 0 <= j <= m
      invariant |row| == j
      invariant forall t :: 0 <= t < j ==> row[t] == rowEntry(c, i, t)
    {
      row := row + [rowEntry(c, i, j)];
      j := j + 1;
    }
    matrix := matrix + [row];
    i := i + 1;
  }
}

// </vc-code>
