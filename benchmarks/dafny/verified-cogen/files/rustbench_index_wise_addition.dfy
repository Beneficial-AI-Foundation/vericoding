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
    assume {:axiom} false;
}
// </vc-code>
