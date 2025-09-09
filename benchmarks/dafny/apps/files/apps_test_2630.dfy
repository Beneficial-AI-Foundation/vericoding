Given an m×n grid where 0 represents empty cell and 1 represents obstacle,
find the number of unique paths from top-left (0,0) to bottom-right (m-1,n-1).
Movement is restricted to right and down only, cannot pass through obstacles.

predicate ValidGrid(grid: seq<seq<int>>)
{
    |grid| > 0 && |grid[0]| > 0 &&
    (forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|) &&
    (forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] in {0, 1})
}

function DPPathCount(grid: seq<seq<int>>): int
    requires ValidGrid(grid)
    ensures DPPathCount(grid) >= 0
    ensures grid[0][0] == 1 ==> DPPathCount(grid) == 0
    ensures grid[|grid|-1][|grid[0]|-1] == 1 ==> DPPathCount(grid) == 0
    ensures |grid| == 1 && |grid[0]| == 1 ==> 
            DPPathCount(grid) == (if grid[0][0] == 0 then 1 else 0)
    ensures (forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[0]| ==> grid[i][j] == 0) ==> 
            DPPathCount(grid) == Binomial(|grid| + |grid[0]| - 2, |grid| - 1)
    ensures |grid| == 1 ==> 
            (DPPathCount(grid) > 0 <==> (forall j :: 0 <= j < |grid[0]| ==> grid[0][j] == 0))
    ensures |grid[0]| == 1 ==> 
            (DPPathCount(grid) > 0 <==> (forall i :: 0 <= i < |grid| ==> grid[i][0] == 0))
{
    var m := |grid|;
    var n := |grid[0]|;
    if grid[0][0] == 1 || grid[m-1][n-1] == 1 then 0
    else 
        if m == 1 && n == 1 then 1
        else if m == 1 then 
            if forall j :: 0 <= j < n ==> grid[0][j] == 0 then 1 else 0
        else if n == 1 then
            if forall i :: 0 <= i < m ==> grid[i][0] == 0 then 1 else 0
        else if forall i, j :: 0 <= i < m && 0 <= j < n ==> grid[i][j] == 0 then
            Binomial(m + n - 2, m - 1)
        else
            var path := InitializePath(grid);
            ComputePaths(grid, path, m, n)
}

function Binomial(n: int, k: int): int
    requires n >= 0 && k >= 0
    ensures Binomial(n, k) >= 0
    decreases n, k
{
    if k > n then 0
    else if k == 0 || k == n then 1
    else if k == 1 then n
    else Binomial(n-1, k-1) + Binomial(n-1, k)
}

function InitializePath(grid: seq<seq<int>>): seq<seq<int>>
    requires ValidGrid(grid)
    requires grid[0][0] == 0 && grid[|grid|-1][|grid[0]|-1] == 0
    ensures |InitializePath(grid)| == |grid|
    ensures forall i :: 0 <= i < |grid| ==> |InitializePath(grid)[i]| == |grid[0]|
    ensures forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[0]| ==> InitializePath(grid)[i][j] >= 0
{
    var m := |grid|;
    var n := |grid[0]|;
    var path := seq(m, i => seq(n, j => 0));
    var pathWithCol := InitializeColumn(grid, path, 0, m);
    InitializeRow(grid, pathWithCol, 1, n)
}

function InitializeColumn(grid: seq<seq<int>>, path: seq<seq<int>>, i: int, m: int): seq<seq<int>>
    requires ValidGrid(grid) && m == |grid|
    requires |path| == m && forall k :: 0 <= k < m ==> |path[k]| == |grid[0]|
    requires forall k, j :: 0 <= k < m && 0 <= j < |grid[0]| ==> path[k][j] >= 0
    requires 0 <= i <= m
    ensures |InitializeColumn(grid, path, i, m)| == m
    ensures forall k :: 0 <= k < m ==> |InitializeColumn(grid, path, i, m)[k]| == |grid[0]|
    ensures forall k, j :: 0 <= k < m && 0 <= j < |grid[0]| ==> InitializeColumn(grid, path, i, m)[k][j] >= 0
    decreases m - i
{
    if i >= m then path
    else if grid[i][0] == 1 then path
    else 
        var newPath := path[i := path[i][0 := 1]];
        InitializeColumn(grid, newPath, i + 1, m)
}

function InitializeRow(grid: seq<seq<int>>, path: seq<seq<int>>, j: int, n: int): seq<seq<int>>
    requires ValidGrid(grid) && n == |grid[0]|
    requires |path| == |grid| && forall k :: 0 <= k < |grid| ==> |path[k]| == n
    requires forall k, l :: 0 <= k < |grid| && 0 <= l < n ==> path[k][l] >= 0
    requires 1 <= j <= n
    ensures |InitializeRow(grid, path, j, n)| == |grid|
    ensures forall k :: 0 <= k < |grid| ==> |InitializeRow(grid, path, j, n)[k]| == n
    ensures forall k, l :: 0 <= k < |grid| && 0 <= l < n ==> InitializeRow(grid, path, j, n)[k][l] >= 0
    decreases n - j
{
    if j >= n then path
    else if grid[0][j] == 1 then path
    else 
        var newPath := path[0 := path[0][j := 1]];
        InitializeRow(grid, newPath, j + 1, n)
}

function ComputePaths(grid: seq<seq<int>>, path: seq<seq<int>>, m: int, n: int): int
    requires ValidGrid(grid) && m == |grid| && n == |grid[0]|
    requires |path| == m && forall i :: 0 <= i < m ==> |path[i]| == n
    requires forall i, j :: 0 <= i < m && 0 <= j < n ==> path[i][j] >= 0
    ensures ComputePaths(grid, path, m, n) >= 0
{
    var finalPath := FillDPTable(grid, path, 1, 1, m, n);
    finalPath[m-1][n-1]
}

function FillDPTable(grid: seq<seq<int>>, path: seq<seq<int>>, i: int, j: int, m: int, n: int): seq<seq<int>>
    requires ValidGrid(grid) && m == |grid| && n == |grid[0]|
    requires |path| == m && forall k :: 0 <= k < m ==> |path[k]| == n
    requires forall k, l :: 0 <= k < m && 0 <= l < n ==> path[k][l] >= 0
    requires 1 <= i <= m && 1 <= j <= n
    ensures |FillDPTable(grid, path, i, j, m, n)| == m
    ensures forall k :: 0 <= k < m ==> |FillDPTable(grid, path, i, j, m, n)[k]| == n
    ensures forall k, l :: 0 <= k < m && 0 <= l < n ==> FillDPTable(grid, path, i, j, m, n)[k][l] >= 0
    decreases m - i, n - j
{
    if i >= m then path
    else if j >= n then FillDPTable(grid, path, i + 1, 1, m, n)
    else
        var newValue := if grid[i][j] != 1 then path[i-1][j] + path[i][j-1] else 0;
        var newPath := path[i := path[i][j := newValue]];
        FillDPTable(grid, newPath, i, j + 1, m, n)
}

method uniquePathsWithObstacles(obstacleGrid: seq<seq<int>>) returns (result: int)
    requires ValidGrid(obstacleGrid)
    ensures result >= 0
    ensures obstacleGrid[0][0] == 1 ==> result == 0
    ensures obstacleGrid[|obstacleGrid|-1][|obstacleGrid[0]|-1] == 1 ==> result == 0
    ensures |obstacleGrid| == 1 && |obstacleGrid[0]| == 1 ==> 
            result == (if obstacleGrid[0][0] == 0 then 1 else 0)
    ensures result == DPPathCount(obstacleGrid)
    ensures (forall i, j :: 0 <= i < |obstacleGrid| && 0 <= j < |obstacleGrid[0]| ==> obstacleGrid[i][j] == 0) ==> 
            result == Binomial(|obstacleGrid| + |obstacleGrid[0]| - 2, |obstacleGrid| - 1)
    ensures |obstacleGrid| == 1 ==> 
            (result > 0 <==> (forall j :: 0 <= j < |obstacleGrid[0]| ==> obstacleGrid[0][j] == 0))
    ensures |obstacleGrid[0]| == 1 ==> 
            (result > 0 <==> (forall i :: 0 <= i < |obstacleGrid| ==> obstacleGrid[i][0] == 0))
{
    result := DPPathCount(obstacleGrid);
}
