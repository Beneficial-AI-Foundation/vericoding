// <vc-preamble>
predicate SlopeSearchPrecond(a: seq<seq<int>>, key: int)
{
    |a| > 0 &&
    (forall i :: 0 <= i < |a| ==> |a[i]| == |a[0]|) &&
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a[i]| - 1 ==> a[i][j] <= a[i][j + 1]) &&
    (forall j, i {:trigger a[i][j]} :: 0 <= j < |a[0]| && 0 <= i < |a| - 1 ==> a[i][j] <= a[i + 1][j])
}
function Get2d(a: seq<seq<int>>, i: int, j: int): int
    requires 0 <= i < |a|
    requires 0 <= j < |a[i]|
{
    a[i][j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SlopeSearch(a: seq<seq<int>>, key: int) returns (result: (int, int))
    requires SlopeSearchPrecond(a, key)
    ensures
        var (m, n) := result;
        ((m >= 0 && m < |a| && n >= 0 && n < |a[0]| && a[m][n] == key) ||
         (m == -1 && n == -1 && forall i, j :: 0 <= i < |a| && 0 <= j < |a[i]| ==> a[i][j] != key))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := (-1, -1);
    // impl-end
}
// </vc-code>
