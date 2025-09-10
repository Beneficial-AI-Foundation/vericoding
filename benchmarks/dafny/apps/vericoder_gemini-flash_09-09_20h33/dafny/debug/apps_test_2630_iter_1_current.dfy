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
function method ComputePaths(grid: seq<seq<int>>, path: seq<seq<int>>, m: int, n: int): int
    requires m == |grid| && n == |grid[0]|
    requires (forall i :: 0 <= i < m ==> |path[i]| == n)
    requires (forall i, j :: 0 <= i < m && 0 <= j < n ==> path[i][j] == 0)
    requires (forall i, j :: 0 <= i < m && 0 <= j < n ==> grid[i][j] in {0, 1})
    requires grid[0][0] == 0 && grid[m-1][n-1] == 0
    ensures ComputePaths(grid, path, m, n) >= 0
    decreases m*n
{
    var dp := new int[m][n];

    // Initialize the first row and first column
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall k :: 0 <= k < i ==> dp[k][0] == (if grid[k][0] == 0 then 1 else 0))
        invariant (forall k :: 0 <= k < i ==> (forall l :: 0 <= l < n ==> grid[k][l] in {0,1}))
    {
        if grid[i][0] == 1 && i == 0 then
            dp[i][0] := 0;
        else if grid[i][0] == 1 then
            dp[i][0] := 0;
            // Any cell below an obstacle in the first column is unreachable
            var x := i + 1;
            while x < m
                invariant 0 <= x <= m
                invariant i < x
                invariant dp[i][0] == 0
                invariant (forall k :: i < k < x ==> dp[k][0] == 0)
            {
                dp[x][0] := 0;
                x := x + 1;
            }
            break; // Stop initializing the first column if an obstacle is encountered
        else if i == 0 || dp[i-1][0] == 1 then // Check if the path to this cell is blocked
            dp[i][0] := 1;
        else
            dp[i][0] := 0; // If previous cell in first column was obstacle (dp[i-1][0] == 0), then this is also 0
        i := i + 1;
    }
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant (forall l :: 0 <= l < j ==> dp[0][l] == (if grid[0][l] == 0 && (l == 0 || dp[0][l-1] == 1) then 1 else 0))
        invariant (forall l :: 0 <= l < j ==> (forall k :: 0 <= k < m ==> grid[k][l] in {0,1}))
    {
        if grid[0][j] == 1 && j == 0 then
            dp[0][j] := 0;
        else if grid[0][j] == 1 then
            dp[0][j] := 0;
            // Any cell to the right of an obstacle in the first row is unreachable
            var y := j + 1;
            while y < n
                invariant 0 <= y <= n
                invariant j < y
                invariant dp[0][j] == 0
                invariant (forall k :: j < k < y ==> dp[0][k] == 0)
            {
                dp[0][y] := 0;
                y := y + 1;
            }
            break; // Stop initializing the first row if an obstacle is encountered
        else if j == 0 || dp[0][j-1] == 1 then // Check if the path to this cell is blocked
            dp[0][j] := 1;
        else
            dp[0][j] := 0; // If previous cell in first row was obstacle (dp[0][j-1] == 0), then this is also 0
        j := j + 1;
    }
    
    // Compute paths for the rest of the grid
    i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> grid[r][c] in {0,1}))
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
        invariant (forall r :: 0 < r < i ==> (forall c :: 0 < c < n ==> dp[r][c] == (if grid[r][c] == 0 then dp[r-1][c] + dp[r][c-1] else 0)))
        invariant (forall r :: 0 < r < i ==> dp[r][0] == (if grid[r][0] == 0 then dp[r-1][0] else 0))
        invariant (forall c :: 0 < c < n ==> dp[0][c] == (if grid[0][c] == 0 then dp[0][c-1] else 0))
    {
        j := 1;
        while j < n
            invariant 1 <= j <= n
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> grid[r][c] in {0,1}))
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
            invariant (forall r :: 0 < r < i ==> (forall c :: 0 < c < n ==> dp[r][c] == (if grid[r][c] == 0 then dp[r-1][c] + dp[r][c-1] else 0)))
            invariant (forall c :: 0 < c < j ==> dp[i][c] == (if grid[i][c] == 0 then dp[i-1][c] + dp[i][c-1] else 0))
            // The first row and column initialization must be correct for the current row/column being computed
            invariant dp[i][0] == (if grid[i][0] == 0 then dp[i-1][0] else 0)
            invariant dp[0][j] == (if grid[0][j] == 0 then dp[0][j-1] else 0)
        {
            if grid[i][j] == 1 then
                dp[i][j] := 0;
            else
                dp[i][j] := dp[i-1][j] + dp[i][j-1];
            j := j + 1;
        }
        i := i + 1;
    }
    return dp[m-1][n-1];
}

function InitializePath(grid: seq<seq<int>>): seq<seq<int>>
    requires ValidGrid(grid)
    ensures var m := |grid|; var n := |grid[0]|;
            |InitializePath(grid)| == m && (forall i :: 0 <= i < m ==> |InitializePath(grid)[i]| == n) &&
            (forall i, j :: 0 <= i < m && 0 <= j < n ==> InitializePath(grid)[i][j] == 0)
{
    var m := |grid|;
    var n := |grid[0]|;
    var path := new int[m][n];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> path[r][c] == 0))
    {
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant (forall c :: 0 <= c < j ==> path[i][c] == 0)
        {
            path[i][j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    return path;
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
    var m := |obstacleGrid>;
    var n := |obstacleGrid[0]|;
    if obstacleGrid[0][0] == 1 || obstacleGrid[m-1][n-1] == 1 then 0
    else 
        if m == 1 && n == 1 then 1
        else if m == 1 then 
            if forall j :: 0 <= j < n ==> obstacleGrid[0][j] == 0 then 1 else 0
        else if n == 1 then
            if forall i :: 0 <= i < m ==> obstacleGrid[i][0] == 0 then 1 else 0
        else if forall i, j :: 0 <= i < m && 0 <= j < n ==> obstacleGrid[i][j] == 0 then
            Binomial(m + n - 2, m - 1)
        else
            var path := InitializePath(obstacleGrid);
            return ComputePaths(obstacleGrid, path, m, n);
}
// </vc-code>

