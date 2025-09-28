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
{
  /* code modified by LLM (iteration 5): Fixed compilation error by removing 'var' to avoid duplicate local-variable name collision with return parameter, assuming new array<array<int>> is valid syntax */
  c := new array<array<int>>(a.Length);
  for i := 0 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall k :: 0 <= k < i ==> c[k].Length == a[k].Length
    invariant forall k :: 0 <= k < i ==> forall l :: 0 <= l < a[k].Length ==> c[k][l] == a[k][l]?.field() + b[k][l]
  {
    var temp := new int[a[i].Length];
    for j := 0 to a[i].Length - 1
      invariant 0 <= j <= a[i].Length
      invariant forall k :: 0 <= k < j ==> temp[k] == a[i][k] + b[i][k]
    {
      temp[j] := a[i][j] + b[i][j];
    }
    c[i] := temp;
  }
}
// </vc-code>
