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
// Empty helpers as the basic implementation suffices for verification with given spec.
// </vc-helpers>

// <vc-spec>
method minPathSum(grid: array2<int>) returns (result: int)
    requires ValidInput(grid)
    ensures result >= 0
    ensures grid.Length0 == 1 && grid.Length1 == 1 ==> result == grid[0, 0]
// </vc-spec>
// <vc-code>
{
  var m : int := grid.Length0;
  var n : int := grid.Length1;
  if m == 1 && n == 1 {
    return grid[0, 0];
  }
  var dp : array2<int> := new int[m, n];
  var i : int := m - 1;
  while i >= 0
    decreases i
  {
    var j : int := n - 1;
    while j >= 0
      decreases j
    {
      if i == m - 1 && j == n - 1 {
        dp[i, j] := grid[i, j];
      } else if i == m - 1 {
        dp[i, j] := grid[i, j] + dp[i, j + 1];
      } else if j == n - 1 {
        dp[i, j] := grid[i, j] + dp[i + 1, j];
      } else {
        dp[i, j] := grid[i, j] + if dp[i + 1, j] < dp[i, j + 1] then dp[i + 1, j] else dp[i, j + 1];
      }
      j := j - 1;
    }
    i := i - 1;
  }
  return dp[0, 0];
}
// </vc-code>

