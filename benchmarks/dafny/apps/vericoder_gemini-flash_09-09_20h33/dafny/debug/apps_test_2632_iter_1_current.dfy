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
function min(a: int, b: int): int {
    if a < b then a else b
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

    if m == 0 || n == 0 {
        return 0; // Should not happen given ValidInput implies m,n > 0
    }

    var dp := new array2<int>(m, n);

    dp[0, 0] := grid[0, 0];

    // Initialize first column
    for i := 1 to m - 1 {
        dp[i, 0] := dp[i - 1, 0] + grid[i, 0];
    }

    // Initialize first row
    for j := 1 to n - 1 {
        dp[0, j] := dp[0, j - 1] + grid[0, j];
    }

    // Fill the rest of the DP table
    for i := 1 to m - 1 {
        for j := 1 to n - 1 {
            dp[i, j] := min(dp[i - 1, j], dp[i, j - 1]) + grid[i, j];
        }
    }

    return dp[m - 1, n - 1];
}
// </vc-code>

