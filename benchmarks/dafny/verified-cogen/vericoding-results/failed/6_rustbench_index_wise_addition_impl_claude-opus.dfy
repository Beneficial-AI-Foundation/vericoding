// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Added modifies clause and fixed array allocation */
{
  c := new array<int>[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall k :: 0 <= k < i ==> c[k] != null
    invariant forall k :: 0 <= k < i ==> c[k].Length == a[k].Length
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < c[k].Length ==> c[k][j] == a[k][j] + b[k][j]
    invariant forall k :: i <= k < a.Length ==> c[k] == null
  {
    var row := new int[a[i].Length];
    var j := 0;
    while j < a[i].Length
      invariant 0 <= j <= a[i].Length
      invariant row.Length == a[i].Length
      invariant forall k :: 0 <= k < j ==> row[k] == a[i][k] + b[i][k]
      modifies row
    {
      row[j] := a[i][j] + b[i][j];
      j := j + 1;
    }
    c[i] := row;
    i := i + 1;
  }
}
// </vc-code>
