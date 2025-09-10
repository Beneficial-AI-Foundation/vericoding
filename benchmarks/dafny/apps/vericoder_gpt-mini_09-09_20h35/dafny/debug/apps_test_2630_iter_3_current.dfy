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

// <vc-helpers>
function InitializePath(grid: seq<seq<int>>): seq<seq<int>>
    requires ValidGrid(grid)
    ensures |InitializePath(grid)| == |grid|
    ensures forall i :: 0 <= i < |grid| ==> |InitializePath(grid)[i]| == |grid[0]|
    ensures InitializePath(grid)[0][0] == 1
    ensures forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[0]| && !(i == 0 && j == 0) ==> InitializePath(grid)[i][j] == 0
{
    var m := |grid|;
    var n := |grid[0]|;
    seq i | 0 <= i < m :: (seq j | 0 <= j < n :: (if i == 0 && j == 0 then 1 else 0))
}

function Count(grid: seq<seq<int>>, i: int, j: int): int
    requires ValidGrid(grid)
    requires 0 <= i < |grid|
    requires 0 <= j < |grid[0]|
    ensures Count(grid,i,j) >= 0
    decreases i + j
{
    if grid[i][j] == 1 then 0
    else if i == 0 && j == 0 then 1
    else if i == 0 then Count(grid, 0, j-1)
    else if j == 0 then Count(grid, i-1, 0)
    else Count(grid, i-1, j) + Count(grid, i, j-1)
}

function ComputePaths(grid: seq<seq<int>>, path: seq<seq<int>>, m: int, n: int): int
    requires ValidGrid(grid)
    requires m == |grid|
    requires n == |grid[0]|
    requires |path| == m
    requires forall i :: 0 <= i < m ==> |path[i]| == n
    ensures ComputePaths(grid, path, m, n) >= 0
    ensures ComputePaths(grid, path, m, n) == Count(grid, m-1, n-1)
{
    Count(grid, m-1, n-1)
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    result := DPPathCount(obstacleGrid);
}
// </vc-code>

