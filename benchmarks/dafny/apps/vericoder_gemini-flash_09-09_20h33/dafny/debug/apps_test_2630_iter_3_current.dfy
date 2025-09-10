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
    ensures var m := |grid|; var n := |grid[0]|;
            |InitializePath(grid)| == m && (forall i :: 0 <= i < m ==> |InitializePath(grid)[i]| == n) &&
            (forall i, j :: 0 <= i < m && 0 <= j < n ==> InitializePath(grid)[i][j] == 0)
{
    var m := |grid|;
    var n := |grid[0]|;
    var path := new seq<int>[m];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall r :: 0 <= r < i ==> path[r] != null && |path[r]| == n && (forall c :: 0 <= c < n ==> path[r][c] == 0))
    {
        path[i] := new seq<int>(n, _ => 0);
        i := i + 1;
    }
    return path;
}

method ComputePaths(grid: seq<seq<int>>, path: seq<seq<int>>, m: int, n: int) returns (count: int)
    requires m == |grid| && n == |grid[0]|
    requires m > 0 && n > 0
    requires (forall i :: 0 <= i < m ==> |path[i]| == n)
    requires (forall i, j :: 0 <= i < m && 0 <= j < n ==> path[i][j] == 0)
    requires (forall i, j :: 0 <= i < m && 0 <= j < n ==> grid[i][j] in {0, 1})
    requires grid[0][0] == 0 && grid[m-1][n-1] == 0
    ensures count >= 0
{
    var dp := new seq<int>[m];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall r :: 0 <= r < i ==> dp[r] != null && |dp[r]| == n)
    {
        dp[i] := new seq<int>(n, _ => 0);
        i := i + 1;
    }

    // Initialize the first row and first column
    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall k :: 0 <= k < i ==> dp[k][0] >= 0)
        invariant (forall k :: 0 <= k < i && grid[k][0] == 1 ==> dp[k][0] == 0)
        invariant (forall k :: 0 < k < i && dp[k-1][0] == 0 ==> dp[k][0] == 0)
        invariant (forall k :: 0 < k < i && dp[k-1][0] == 1 && grid[k][0] == 0 ==> dp[k][0] == 1)
    {
        if grid[i][0] == 1 then
            dp[i][0] := 0;
            // Any cell below an obstacle in the first column is unreachable
            var x := i + 1;
            while x < m
                invariant i < x <= m
                invariant dp[i][0] == 0
                invariant (forall k :: i < k < x ==> dp[k][0] == 0)
            {
                dp[k][0] := 0;
                x := x + 1;
            }
            break; 
        else if i == 0 then
            dp[i][0] := 1;
            assert dp[0][0] == 1; // Explicit assertion
        else if dp[i-1][0] == 1 then 
            dp[i][0] := 1;
        else
            dp[i][0] := 0; 
        i := i + 1;
    }
    
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant (forall l :: 0 <= l < j ==> dp[0][l] >= 0)
        invariant (forall l :: 0 <= l < j && grid[0][l] == 1 ==> dp[0][l] == 0)
        invariant (forall l :: 0 < l < j && dp[0][l-1] == 0 ==> dp[0][l] == 0)
        invariant (forall l :: 0 < l < j && dp[0][l-1] == 1 && grid[0][l] == 0 ==> dp[0][l] == 1)
    {
        if grid[0][j] == 1 then
            dp[0][j] := 0;
            // Any cell to the right of an obstacle in the first row is unreachable
            var y := j + 1;
            while y < n
                invariant j < y <= n
                invariant dp[0][j] == 0
                invariant (forall k :: j < k < y ==> dp[0][k] == 0)
            {
                dp[0][k] := 0;
                y := y + 1;
            }
            break; 
        else if j == 0 then
            // dp[0][0] is handled by the first loop. If it's 0, it means grid[0][0] was 1,
            // and the loop for 'i' set it to 0 and broke.
            // If grid[0][0] was 0, the 'i' loop should have set dp[0][0] to 1.
            // We should not overwrite it here.
            // However, the specification for first column requires dp[0][0] to be 0 or 1.
            // The condition grid[0][0] == 0 ensures dp[0][0] has been previously set to 1.
            // We do not need `dp[0][j] := 1;` here either for j == 0.
            if (i == 0) { // This means first loop broke early or i didn't run, check dp[0][0] to ensure it is 1 if grid[0][0] is 0
                if dp[0][0] == 0 && grid[0][0] == 0 { // If grid starts at 0, dp[0][0] should be 1
                    dp[0][0] := 1;
                }
            } else if dp[0][j-1] == 1 then 
                dp[0][j] := 1;
            else
                dp[0][j] := 0; 
        else if dp[0][j-1] == 1 then 
            dp[0][j] := 1;
        else
            dp[0][j] := 0; 
        j := j + 1;
    }
    
    // Compute paths for the rest of the grid
    i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
        invariant (forall r :: 0 < r < i ==> (forall c :: 0 < c < n ==> dp[r][c] == (if grid[r][c] == 0 then (dp[r-1][c] + dp[r][c-1]) else 0)))
        invariant (forall r :: 0 < r < i ==> dp[r][0] == (if grid[r][0] == 0 then dp[r-1][0] else 0))
        invariant (forall c :: 0 <= c < n ==> dp[0][c] == (if grid[0][c] == 0 then (if c == 0 then 1 else if dp[0][c-1] == 1 then 1 else 0) else 0))
    {
        j := 1;
        while j < n
            invariant 1 <= j <= n
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
            invariant (forall r :: 0 < r < i ==> (forall c :: 0 < c < n ==> dp[r][c] == (if grid[r][c] == 0 then (dp[r-1][c] + dp[r][c-1]) else 0)))
            invariant (forall c :: 0 < c < j ==> dp[i][c] == (if grid[i][c] == 0 then (dp[i-1][c] + dp[i][c-1]) else 0))
            invariant dp[i][0] == (if grid[i][0] == 0 then dp[i-1][0] else 0)
            invariant dp[0][j] == (if grid[0][j] == 0 then (if j == 0 then 1 else if dp[0][j-1] == 1 then 1 else 0) else 0)
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
    if obstacleGrid[0][0] == 1 || obstacleGrid[m-1][n-1] == 1 then 
        result := 0;
    else if m == 1 && n == 1 then 
        result := 1;
    else if m == 1 then 
        if forall j :: 0 <= j < n ==> obstacleGrid[0][j] == 0 then 
            result := 1; 
        else 
            result := 0;
    else if n == 1 then
        if forall i :: 0 <= i < m ==> obstacleGrid[i][0] == 0 then 
            result := 1; 
        else 
            result := 0;
    else if forall i, j :: 0 <= i < m && 0 <= j < n ==> obstacleGrid[i][j] == 0 then
        result := Binomial(m + n - 2, m - 1);
    else
        var path := InitializePath(obstacleGrid);
        result := ComputePaths(obstacleGrid, path, m, n);
}
// </vc-code>

