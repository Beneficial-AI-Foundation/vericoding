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
    ensures forall i :: 0 <= i < |InitializePath(grid)| ==> |InitializePath(grid)[i]| == |grid[0]|
    ensures forall i, j :: 0 <= i < |InitializePath(grid)| && 0 <= j < |InitializePath(grid)[i]| ==> 
            InitializePath(grid)[i][j] >= 0
{
    var m := |grid|;
    var n := |grid[0]|;
    if grid[0][0] == 1 then 
        seq(m, i => seq(n, j => 0))
    else
        var firstRow := BuildFirstRow(grid, n);
        var firstCol := BuildFirstCol(grid, m);
        seq(m, i => if i == 0 then firstRow else seq(n, j => if j == 0 then firstCol[i] else 0))
}

function BuildFirstRow(grid: seq<seq<int>>, n: int): seq<int>
    requires ValidGrid(grid)
    requires 0 <= n <= |grid[0]|
    ensures |BuildFirstRow(grid, n)| == n
    ensures forall j :: 0 <= j < n ==> BuildFirstRow(grid, n)[j] >= 0
    decreases n
{
    if n == 0 then []
    else if n == 1 then [if grid[0][0] == 1 then 0 else 1]
    else 
        var prev := BuildFirstRow(grid, n-1);
        prev + [if grid[0][n-1] == 1 then 0 else if |prev| > 0 && prev[|prev|-1] > 0 then 1 else 0]
}

function BuildFirstCol(grid: seq<seq<int>>, m: int): seq<int>
    requires ValidGrid(grid)
    requires 0 <= m <= |grid|
    ensures |BuildFirstCol(grid, m)| == m
    ensures forall i :: 0 <= i < m ==> BuildFirstCol(grid, m)[i] >= 0
    decreases m
{
    if m == 0 then []
    else if m == 1 then [if grid[0][0] == 1 then 0 else 1]
    else 
        var prev := BuildFirstCol(grid, m-1);
        prev + [if grid[m-1][0] == 1 then 0 else if |prev| > 0 && prev[|prev|-1] > 0 then 1 else 0]
}

function ComputePaths(grid: seq<seq<int>>, path: seq<seq<int>>, m: int, n: int): int
    requires ValidGrid(grid)
    requires 0 < m <= |grid| && 0 < n <= |grid[0]|
    requires |path| == |grid| && forall i :: 0 <= i < |path| ==> |path[i]| == |grid[0]|
    requires forall i, j :: 0 <= i < |path| && 0 <= j < |path[i]| ==> path[i][j] >= 0
    ensures ComputePaths(grid, path, m, n) >= 0
    decreases m * n
{
    if m == 1 && n == 1 then path[0][0]
    else if m == 1 then path[0][n-1]
    else if n == 1 then path[m-1][0]
    else
        var updatedPath := UpdatePath(grid, path, 1, 1, m, n);
        updatedPath[m-1][n-1]
}

function UpdatePath(grid: seq<seq<int>>, path: seq<seq<int>>, i: int, j: int, m: int, n: int): seq<seq<int>>
    requires ValidGrid(grid)
    requires 0 < m <= |grid| && 0 < n <= |grid[0]|
    requires |path| == |grid| && forall k :: 0 <= k < |path| ==> |path[k]| == |grid[0]|
    requires 1 <= i <= m && 1 <= j <= n + 1
    requires forall r, c :: 0 <= r < |path| && 0 <= c < |path[r]| ==> path[r][c] >= 0
    ensures |UpdatePath(grid, path, i, j, m, n)| == |path|
    ensures forall k :: 0 <= k < |UpdatePath(grid, path, i, j, m, n)| ==> 
            |UpdatePath(grid, path, i, j, m, n)[k]| == |path[0]|
    ensures forall r, c :: 0 <= r < |UpdatePath(grid, path, i, j, m, n)| && 
            0 <= c < |UpdatePath(grid, path, i, j, m, n)[r]| ==> 
            UpdatePath(grid, path, i, j, m, n)[r][c] >= 0
    decreases (m - i) * n + (n - j + 1)
{
    if i >= m then path
    else if j >= n then 
        if i + 1 <= m then
            UpdatePath(grid, path, i+1, 1, m, n)
        else
            path
    else if grid[i][j] == 1 then
        var newPath := path[i := path[i][j := 0]];
        UpdatePath(grid, newPath, i, j+1, m, n)
    else
        var value := if i == 0 then path[0][j] 
                    else if j == 0 then path[i][0]
                    else path[i-1][j] + path[i][j-1];
        var newPath := path[i := path[i][j := value]];
        UpdatePath(grid, newPath, i, j+1, m, n)
}

method ComputePathsIterative(grid: seq<seq<int>>, path: array2<int>, m: int, n: int)
    requires ValidGrid(grid)
    requires path.Length0 == |grid| && path.Length1 == |grid[0]|
    requires 0 < m <= |grid| && 0 < n <= |grid[0]|
    requires forall i, j :: 0 <= i < m && 0 <= j < n ==> path[i, j] >= 0
    modifies path
    ensures path[m-1, n-1] >= 0
    ensures forall i, j :: 0 <= i < m && 0 <= j < n ==> path[i, j] >= 0
{
    var i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant forall r, c :: 0 <= r < m && 0 <= c < n ==> path[r, c] >= 0
    {
        var j := 1;
        while j < n
            invariant 1 <= j <= n
            invariant forall r, c :: 0 <= r < m && 0 <= c < n ==> path[r, c] >= 0
        {
            if grid[i][j] == 1 {
                path[i, j] := 0;
            } else {
                path[i, j] := path[i-1, j] + path[i, j-1];
            }
            j := j + 1;
        }
        i := i + 1;
    }
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
    var m := |obstacleGrid|;
    var n := |obstacleGrid[0]|;
    
    if obstacleGrid[0][0] == 1 || obstacleGrid[m-1][n-1] == 1 {
        return 0;
    }
    
    if m == 1 && n == 1 {
        return 1;
    }
    
    if m == 1 {
        var allClear := true;
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant allClear <==> (forall k :: 0 <= k < j ==> obstacleGrid[0][k] == 0)
        {
            if obstacleGrid[0][j] == 1 {
                allClear := false;
            }
            j := j + 1;
        }
        return if allClear then 1 else 0;
    }
    
    if n == 1 {
        var allClear := true;
        var i := 0;
        while i < m
            invariant 0 <= i <= m
            invariant allClear <==> (forall k :: 0 <= k < i ==> obstacleGrid[k][0] == 0)
        {
            if obstacleGrid[i][0] == 1 {
                allClear := false;
            }
            i := i + 1;
        }
        return if allClear then 1 else 0;
    }
    
    var path := new int[m, n];
    
    // Initialize entire array to 0
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> path[r, c] == 0
    {
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant forall c :: 0 <= c < j ==> path[i, c] == 0
            invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> path[r, c] == 0
        {
            path[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Initialize first cell
    path[0, 0] := 1;
    
    // Initialize first row
    var j := 1;
    while j < n
        invariant 1 <= j <= n
        invariant path[0, 0] == 1
        invariant forall c :: 0 <= c < j ==> path[0, c] >= 0
        invariant forall r, c :: 0 <= r < m && 0 <= c < n ==> path[r, c] >= 0
    {
        if obstacleGrid[0][j] == 1 {
            path[0, j] := 0;
        } else {
            path[0, j] := path[0, j-1];
        }
        j := j + 1;
    }
    
    // Initialize first column
    i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant forall r :: 0 <= r < i ==> path[r, 0] >= 0
        invariant forall r, c :: 0 <= r < m && 0 <= c < n ==> path[r, c] >= 0
    {
        if obstacleGrid[i][0] == 1 {
            path[i, 0] := 0;
        } else {
            path[i, 0] := path[i-1, 0];
        }
        i := i + 1;
    }
    
    // Fill the rest of the table
    ComputePathsIterative(obstacleGrid, path, m, n);
    
    result := path[m-1, n-1];
}
// </vc-code>

