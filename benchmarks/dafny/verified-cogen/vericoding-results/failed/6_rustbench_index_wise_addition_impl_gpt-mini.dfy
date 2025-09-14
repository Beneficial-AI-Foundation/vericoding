// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer addition helper */
function SumInt(x: int, y: int): int { x + y }
// </vc-helpers>

// <vc-spec>
method IndexWiseAddition(a: array<array<int>>, b: array<array<int>>) returns (c: array<array<int>>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < a.Length ==> a[i].Length == b[i].Length
    requires forall i :: 0 <= i < a.Length ==> forall j :: 0 <= j < a[i].Length ==> a[i][j] + b[i][j] <= 2147483647
    requires forall i :: 0 <= i < a.Length ==> forall j :: 0 <= j < a[i].Length ==> a[i][j] + b[i][j] >= -2147483648
    ensures c.Length == a.Length
    ensures forall i :: 0 <= i < c.Length ==> c[i].Length == a[i].Length
    ensures forall i :: 0 <= i < c.Length ==> forall j :: 0 <= j < c[i].Length ==> c[i][j] == a[i][j] + b[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): allocate outer array and compute per-row sums */
  c := new array<array<int>>(a.Length);
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall k :: 0 <= k < i ==> c[k] != null && c[k].Length == a[k].Length && (forall j :: 0 <= j < c[k].Length ==> c[k][j] == a[k][j] + b[k][j])
  {
    var rowLen := a[i].Length;
    var row := new int[rowLen];
    var j := 0;
    while j < rowLen
      invariant 0 <= j <= rowLen
      invariant row.Length == rowLen
      invariant forall jj :: 0 <= jj < j ==> row[jj] == a[i][jj] + b[i][jj]
    {
      row[j] := SumInt(a[i][j], b[i][j]);
      j := j + 1;
    }
    c[i] := row;
    i := i + 1;
  }
}
// </vc-code>
