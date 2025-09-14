// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified reusable row-wise sum predicate with null-safety */
predicate RowSumOK(aRow: array<int>, bRow: array<int>, cRow: array<int>)
  reads aRow, bRow, cRow
{
  cRow != null &&
  aRow != null &&
  bRow != null &&
  cRow.Length == aRow.Length &&
  aRow.Length == bRow.Length &&
  (forall j :: 0 <= j < cRow.Length ==> cRow[j] == aRow[j] + bRow[j])
}
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
  /* code modified by LLM (iteration 5): implement row-by-row addition with explicit invariants avoiding helper predicate */
  c := new (array<int>)[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall t :: 0 <= t < i ==> c[t] != null && c[t].Length == a[t].Length && a[t].Length == b[t].Length && (forall j :: 0 <= j < a[t].Length ==> c[t][j] == a[t][j] + b[t][j])
    decreases a.Length - i
  {
    var rowA := a[i];
    var rowB := b[i];
    var len := rowA.Length;
    assert len == rowB.Length;
    var rowC := new int[len];
    var j := 0;
    while j < len
      invariant 0 <= j <= len
      invariant rowC != null && rowC.Length == len
      invariant forall k :: 0 <= k < j ==> rowC[k] == rowA[k] + rowB[k]
      decreases len - j
    {
      rowC[j] := rowA[j] + rowB[j];
      j := j + 1;
    }
    c[i] := rowC;
    i := i + 1;
  }
}
// </vc-code>
