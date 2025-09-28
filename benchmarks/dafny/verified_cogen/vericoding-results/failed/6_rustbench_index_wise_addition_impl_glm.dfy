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
  /* code modified by LLM (iteration 5): fixed array initialization by creating outer array of nulls and then initializing inner arrays in a loop */
  c := new arrayarray<int>>(a.Length);
  var i := 0;
  while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> c[j] != null && c[j].Length == a[j].Length
      invariant forall j :: 0 <= j < i ==> forall k :: 0 <= k < c[j].Length ==> c[j][k] == a[j][k] + b[j][k]
  {
      c[i] := new array<int>(a[i].Length);
      var j := 0;
      while j < a[i].Length
          invariant 0 <= j <= a[i].Length
          invariant forall k :: 0 <= k < j ==> c[i][k] == a[i][k] + b[i][k]
      {
          c[i][j] := a[i][j] + b[i][j];
          j := j + 1;
      }
      i := i + 1;
  }
}
// </vc-code>
