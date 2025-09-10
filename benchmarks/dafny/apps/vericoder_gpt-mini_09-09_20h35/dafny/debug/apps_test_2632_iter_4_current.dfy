predicate ValidPath(path: seq<(int, int)>, m: int, n: int)
{
    |path| >= 1 &&
    path[0] == (0, 0) &&
    path[|path|-1] == (m-1, n-1) &&
    (forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < m && 0 <= path[i].1 < n) &&
    forall i :: 0 <= i < |path|-1 ==> 
        (path[i+1].0 == path[i].0 && path[i+1].1 == path[i].1 + 1) || // right
        (path[i+1].0 == path[i].0 + 1 && path[i+1].1 == path[i].1)    // down
}

function PathSum(path: seq<(int, int)>, grid: array2<int>): int
    requires forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < grid.Length0 && 0 <= path[i].1 < grid.Length1
    reads grid
{
    if |path| == 0 then 0
    else grid[path[0].0, path[0].1] + PathSum(path[1..], grid)
}

predicate ValidInput(grid: array2<int>)
    reads grid
{
    grid.Length0 > 0 && grid.Length1 > 0 &&
    forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> grid[i, j] >= 0
}

// <vc-helpers>
lemma SumNonNeg(a: int, b: int)
    ensures a >= 0 && b >= 0 ==> a + b >= 0
{
}
// </vc-helpers>

// <vc-spec>
method minPathSum(grid: array2<int>) returns (result: int)
    requires ValidInput(grid)
    ensures result >= 0
    ensures grid.Length0 == 1 && grid.Length1 == 1 ==> result == grid[0, 0]
// </vc-spec>
// <vc-code>
{
  var m := grid.Length0;
  var n := grid.Length1;
  var dp := new int[m, n];

  if m == 1 && n == 1 {
    result := grid[0,0];
    return;
  }

  dp[0,0] := grid[0,0];
  assert dp[0,0] >= 0;

  var i := 1;
  while i < m
    invariant 1 <= i <= m
    invariant forall k :: {:trigger dp[k,0]} 0 <= k < i ==> dp[k,0] >= 0
    decreases m - i
  {
    dp[i,0] := dp[i-1,0] + grid[i,0];
    assert dp[i,0] >= 0;
    i := i + 1;
  }

  var j := 1;
  while j < n
    invariant 1 <= j <= n
    invariant forall k :: {:trigger dp[0,k]} 0 <= k < j ==> dp[0,k] >= 0
    decreases n - j
  {
    dp[0,j] := dp[0,j-1] + grid[0,j];
    assert dp[0,j] >= 0;
    j := j + 1;
  }

  // Reestablish simple facts for readability (provable from the above loops)
  assert forall k :: {:trigger dp[k,0]} 0 <= k < m ==> dp[k,0] >= 0;
  assert forall b :: {:trigger dp[0,b]} 0 <= b < n ==> dp[0,b] >= 0;

  i := 1;
  while i < m
    invariant 1 <= i <= m
    invariant forall a, b :: {:trigger dp[a,b]} 0 <= a < i && 0 <= b < n ==> dp[a,b] >= 0
    decreases m - i
  {
    assert dp[i,0] >= 0;
    j := 1;
    while j < n
      invariant 1 <= j <= n
      invariant forall b :: {:trigger dp[i,b]} 0 <= b < j ==> dp[i,b] >= 0
      invariant forall a, b :: {:trigger dp[a,b]} 0 <= a < i && 0 <= b < n ==> dp[a,b] >= 0
      decreases n - j
    {
      var left := dp[i, j-1];
      var up := dp[i-1, j];
      var best := if up < left then up else left;
      dp[i,j] := grid[i,j] + best;
      assert dp[i,j] >= 0;
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[m-1, n-1];
}
// </vc-code>

