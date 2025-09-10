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
lemma PathSumNonNegative(path: seq<(int, int)>, grid: array2<int>)
    requires ValidInput(grid)
    requires forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < grid.Length0 && 0 <= path[i].1 < grid.Length1
    ensures PathSum(path, grid) >= 0
    decreases |path|
{
    if |path| > 0 {
        PathSumNonNegative(path[1..], grid);
    }
}

lemma PathSumCons(path: seq<(int, int)>, grid: array2<int>)
    requires |path| >= 1
    requires forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < grid.Length0 && 0 <= path[i].1 < grid.Length1
    ensures PathSum(path, grid) == grid[path[0].0, path[0].1] + PathSum(path[1..], grid)
{
}

ghost function MinPathSum(grid: array2<int>): int
    requires ValidInput(grid)
    reads grid
    ensures MinPathSum(grid) >= 0
{
    var m := grid.Length0;
    var n := grid.Length1;
    
    if m == 1 && n == 1 {
        grid[0, 0]
    } else {
        var down := if m > 1 then MinPathSum(grid[1.., ..]) + grid[0, 0] else int.MaxValue;
        var right := if n > 1 then MinPathSum(grid[.., 1..]) + grid[0, 0] else int.MaxValue;
        if down <= right then down else right
    }
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
    
    dp[0, 0] := grid[0, 0];
    
    for j := 1 to n-1
        invariant forall k :: 0 <= k < j ==> dp[0, k] >= 0
    {
        dp[0, j] := dp[0, j-1] + grid[0, j];
    }
    
    for i := 1 to m-1
        invariant forall k :: 0 <= k < i ==> forall l :: 0 <= l < n ==> dp[k, l] >= 0
    {
        dp[i, 0] := dp[i-1, 0] + grid[i, 0];
        for j := 1 to n-1
            invariant forall k :: 0 <= k < j ==> dp[i, k] >= 0
        {
            if dp[i-1, j] <= dp[i, j-1] {
                dp[i, j] := dp[i-1, j] + grid[i, j];
            } else {
                dp[i, j] := dp[i, j-1] + grid[i, j];
            }
        }
    }
    
    result := dp[m-1, n-1];
}
// </vc-code>

