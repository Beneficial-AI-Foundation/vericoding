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
/* helper modified by LLM (iteration 2): column monotonicity lemma */
lemma ColumnLe(a: seq<seq<int>>, key: int, j: int, i: int, r: int)
  requires SlopeSearchPrecond(a, key)
  requires 0 <= j < |a[0]|
  requires 0 <= i <= r < |a|
  ensures a[i][j] <= a[r][j]
{
  if i < r {
    ColumnLe(a, key, j, i, r - 1);
    // r-1 is a valid index for the column monotonicity axiom
    assert 0 <= r - 1;
    assert r - 1 < |a| - 1;
    assert a[r - 1][j] <= a[r][j];
    assert a[i][j] <= a[r][j];
  }
}

/* helper modified by LLM (iteration 2): row monotonicity lemma */
lemma RowLe(a: seq<seq<int>>, key: int, i: int, c: int, d: int)
  requires SlopeSearchPrecond(a, key)
  requires 0 <= i < |a|
  requires 0 <= c <= d < |a[0]|
  ensures a[i][c] <= a[i][d]
{
  if c < d {
    RowLe(a, key, i, c, d - 1);
    // use row monotonicity a[i][d-1] <= a[i][d]
    assert 0 <= d - 1;
    assert d - 1 < |a[0]| - 1;
    assert a[i][d - 1] <= a[i][d];
    assert a[i][c] <= a[i][d];
  }
}

/* helper modified by LLM (iteration 2): exclude column by iterating rows to establish the universal property */
lemma ExcludeColumn(a: seq<seq<int>>, key: int, i: int, j: int)
  requires SlopeSearchPrecond(a, key)
  requires 0 <= i < |a|
  requires 0 <= j < |a[0]|
  requires Get2d(a, i, j) > key
  ensures forall r :: i <= r < |a| ==> a[r][j] > key
{
  var r := i;
  while r < |a|
    invariant i <= r <= |a|
    invariant forall r0 :: i <= r0 < r ==> a[r0][j] > key
  {
    ColumnLe(a, key, j, i, r);
    // from ColumnLe we have a[i][j] <= a[r][j]; and a[i][j] > key by precondition
    assert a[i][j] <= a[r][j];
    assert a[r][j] > key;
    r := r + 1;
  }
  // after loop r == |a|, so invariant gives the required forall
  assert forall r0 :: i <= r0 < |a| ==> a[r0][j] > key;
}

/* helper modified by LLM (iteration 2): exclude row by iterating columns to establish the universal property */
lemma ExcludeRow(a: seq<seq<int>>, key: int, i: int, j: int)
  requires SlopeSearchPrecond(a, key)
  requires 0 <= i < |a|
  requires 0 <= j < |a[0]|
  requires Get2d(a, i, j) < key
  ensures forall c :: 0 <= c <= j ==> a[i][c] < key
{
  var c := 0;
  // iterate columns from 0 up to j (inclusive)
  while c <= j
    invariant 0 <= c <= j + 1
    invariant forall cc :: 0 <= cc < c ==> a[i][cc] < key
  {
    RowLe(a, key, i, c, j);
    // from RowLe we have a[i][c] <= a[i][j]; and a[i][j] < key by precondition
    assert a[i][c] <= a[i][j];
    assert a[i][c] < key;
    c := c + 1;
  }
  // when c == j+1 the invariant implies for all 0 <= cc <= j : a[i][cc] < key
  assert forall cc :: 0 <= cc <= j ==> a[i][cc] < key;
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
/* code modified by LLM (iteration 2): slope search implementation using the helpers */
{
  var i := 0;
  var j := |a[0]| - 1;
  while i < |a| && j >= 0
    invariant 0 <= i <= |a|
    invariant -1 <= j < |a[0]|
    invariant forall r, c :: 0 <= r < |a| && 0 <= c < |a[0]| && (r < i || c > j) ==> a[r][c] != key
    decreases |a| - i + j
  {
    var cur := Get2d(a, i, j);
    if cur == key {
      result := (i, j);
      return;
    } else if cur > key {
      ExcludeColumn(a, key, i, j);
      j := j - 1;
    } else {
      ExcludeRow(a, key, i, j);
      i := i + 1;
    }
  }
  // loop exited: by invariant and exit condition no element equals key
  result := (-1, -1);
}

// </vc-code>
