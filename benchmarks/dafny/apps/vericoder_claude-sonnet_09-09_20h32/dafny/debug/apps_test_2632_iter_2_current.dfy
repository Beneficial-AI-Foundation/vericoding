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
{
    if |path| == 0 {
    } else {
        PathSumNonNegative(path[1..], grid);
    }
}

lemma SingleCellPathExists(grid: array2<int>)
    requires grid.Length0 == 1 && grid.Length1 == 1
    ensures ValidPath([(0, 0)], grid.Length0, grid.Length1)
{
}

lemma SingleCellPathSum(grid: array2<int>)
    requires grid.Length0 == 1 && grid.Length1 == 1
    ensures PathSum([(0, 0)], grid) == grid[0, 0]
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
    if grid.Length0 == 1 && grid.Length1 == 1 {
        SingleCellPathExists(grid);
        SingleCellPathSum(grid);
        return grid[0, 0];
    }
    
    var dp := new int[grid.Length0, grid.Length1];
    
    dp[0, 0] := grid[0, 0];
    
    var j := 1;
    while j < grid.Length1
        invariant 1 <= j <= grid.Length1
        invariant dp[0, 0] == grid[0, 0]
        invariant forall k :: 1 <= k < j ==> dp[0, k] >= 0
    {
        dp[0, j] := dp[0, j-1] + grid[0, j];
        j := j + 1;
    }
    
    var i := 1;
    while i < grid.Length0
        invariant 1 <= i <= grid.Length0
        invariant dp[0, 0] == grid[0, 0]
        invariant forall k :: 1 <= k < grid.Length1 ==> dp[0, k] >= 0
        invariant forall k :: 1 <= k < i ==> dp[k, 0] >= 0
    {
        dp[i, 0] := dp[i-1, 0] + grid[i, 0];
        i := i + 1;
    }
    
    i := 1;
    while i < grid.Length0
        invariant 1 <= i <= grid.Length0
        invariant dp[0, 0] == grid[0, 0]
        invariant forall k :: 1 <= k < grid.Length1 ==> dp[0, k] >= 0
        invariant forall k :: 1 <= k < grid.Length0 ==> dp[k, 0] >= 0
        invariant forall ii, jj :: 1 <= ii < i && 1 <= jj < grid.Length1 ==> dp[ii, jj] >= 0
    {
        j := 1;
        while j < grid.Length1
            invariant 1 <= j <= grid.Length1
            invariant dp[0, 0] == grid[0, 0]
            invariant forall k :: 1 <= k < grid.Length1 ==> dp[0, k] >= 0
            invariant forall k :: 1 <= k < grid.Length0 ==> dp[k, 0] >= 0
            invariant forall ii, jj :: 1 <= ii < i && 1 <= jj < grid.Length1 ==> dp[ii, jj] >= 0
            invariant forall jj :: 1 <= jj < j ==> dp[i, jj] >= 0
        {
            var fromTop := dp[i-1, j];
            var fromLeft := dp[i, j-1];
            if fromTop <= fromLeft {
                dp[i, j] := fromTop + grid[i, j];
            } else {
                dp[i, j] := fromLeft + grid[i, j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := dp[grid.Length0-1, grid.Length1-1];
}
// </vc-code>

