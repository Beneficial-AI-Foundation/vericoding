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
function NumCols(a: seq<seq<int>>): nat
    requires |a| > 0
{
    |a[0]|
}
predicate InBounds(a: seq<seq<int>>, i: int, j: int)
{
    0 <= i < |a| && 0 <= j < |a[i]|
}
lemma RowLenEq(a: seq<seq<int>>, key: int, i: int)
    requires SlopeSearchPrecond(a, key)
    requires 0 <= i < |a|
    ensures |a[i]| == |a[0]|
{
}
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
  result := (-1, -1);
  var m := |a|;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant result == (-1, -1)
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < |a[ii]| ==> a[ii][jj] != key
    decreases m - i
  {
    assert 0 <= i < |a|;
    var j := 0;
    while j < |a[i]|
      invariant 0 <= j <= |a[i]|
      invariant result == (-1, -1)
      invariant forall jj :: 0 <= jj < j ==> a[i][jj] != key
      decreases |a[i]| - j
    {
      if a[i][j] == key {
        RowLenEq(a, key, i);
        result := (i, j);
        return;
      }
      j := j + 1;
    }
    assert forall jj :: 0 <= jj < |a[i]| ==> a[i][jj] != key;
    i := i + 1;
  }
}
// </vc-code>
