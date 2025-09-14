// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed, as no helpers are necessary */
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
/* code modified by LLM (iteration 5): Fixed array type constructor syntax. */
{
    var m := a.Length;
    c := new array<array<int>>(m, _ => new array<int>(0)); // Initialize with empty inner arrays (size 0) initially

    for i := 0 to m - 1
        invariant 0 <= i <= m
        invariant c.Length == m
        invariant forall k :: 0 <= k < i ==> c[k] != null && c[k].Length == a[k].Length
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < a[k].Length ==> c[k][j] == a[k][j] + b[k][j]
    {
        var n := a[i].Length;
        c[i] := new array<int>(n); // Now allocate inner array with correct size
        for j := 0 to n - 1
            invariant 0 <= j <= n
            invariant c[i] != null && c[i].Length == n
            invariant forall k :: 0 <= k < j ==> c[i][k] == a[i][k] + b[i][k]
        {
            c[i][j] := a[i][j] + b[i][j];
        }
    }
}
// </vc-code>
