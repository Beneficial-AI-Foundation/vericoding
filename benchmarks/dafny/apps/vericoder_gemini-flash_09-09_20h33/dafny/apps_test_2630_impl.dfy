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

method ComputePaths(grid: seq<seq<int>>, path_placeholder: seq<seq<int>>, m: int, n: int) returns (count: int)
    requires m == |grid| && n == |grid[0]|
    requires m > 0 && n > 0
    // The `path_placeholder` parameter doesn't seem to be used in the original ComputePaths logic.
    // Assuming it's a leftover or intended for a different approach; removing relevance for this implementation.
    // If it was meant for `path` in `InitializePath`, that's fine as it's not actually used here.
    requires (forall i, j :: 0 <= i < m && 0 <= j < n ==> grid[i][j] in {0, 1})
    requires grid[0][0] == 0 && grid[m-1][n-1] == 0  // Crucial pre-conditions for this specific DP logic
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

    // Initialize the first column
    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant (forall k :: 0 <= k < i ==> dp[k][0] >= 0)
        invariant (forall k :: 0 <= k < i && grid[k][0] == 1 ==> dp[k][0] == 0)
        invariant (forall k :: 0 < k < i && dp[k-1][0] == 0 ==> dp[k][0] == 0)
        invariant (forall k :: 0 < k < i && dp[k-1][0] == 1 && grid[k][0] == 0 ==> dp[k][0] == 1)
        invariant (forall k :: 0 < k < i ==> (dp[k][0] == (if grid[k][0] == 0 then dp[k-1][0] else 0)))
        invariant (i == 0 ==> dp[0][0] == 1) || (i > 0 && dp[0][0] == 1) // dp[0][0] initialized by this loop at i=0
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
                dp[x][0] := 0; // Fix: changed dp[k][0] to dp[x][0]
                x := x + 1;
            }
            break; 
        else if i == 0 then
            dp[i][0] := 1;
        else if dp[i-1][0] == 1 then 
            dp[i][0] := 1;
        else
            dp[i][0] := 0; 
        i := i + 1;
    }
    
    // Initialize the first row
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant (forall l :: 0 <= l < j ==> dp[0][l] >= 0)
        invariant (forall l :: 0 <= l < j && grid[0][l] == 1 ==> dp[0][l] == 0)
        invariant (forall l :: 0 < l < j && dp[0][l-1] == 0 ==> dp[0][l] == 0)
        invariant (forall l :: 0 < l < j && dp[0][l-1] == 1 && grid[0][l] == 0 ==> dp[0][l] == 1)
        invariant (j == 0 ==> dp[0][0] == 1) || (j > 0 && dp[0][0] == 1) // dp[0][0] must be 1 if grid[0][0]==0
        invariant (forall l :: 0 < l < j ==> (dp[0][l] == (if grid[0][l] == 0 then dp[0][l-1] else 0)))
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
                dp[0][y] := 0; // Fix: changed dp[0][k] to dp[0][y]
                y := y + 1;
            }
            break; 
        else if j == 0 then
            // dp[0][0] should already be 1 from the first column initialization if grid[0][0] == 0.
            // No assignment needed here for j==0. If the first loop broke, dp[0][0] would be 0 then
            // this loop would also set it to 0. This is desired behaviour for grid[0][0] == 1.
            // If grid[0][0] == 0, the first loop set dp[0][0]=1, which is correct.
            // So if grid[0][0] == 0, we rely on the first loop to have set it to 1.
            // If grid[0][0] == 1, then both loops would set dp[0][0] to 0 and break properly.
            // No explicit assignment for j==0 when grid[0][0] == 0 is needed if the first loop correctly handled it.
            // The pre-condition `grid[0][0] == 0` guarantees `dp[0][0]` will be `1` after the first loop snippet
            // (assuming `m > 0`).

            // This `if (i==0)` branch is problematic as the outer `i` loop might have completed.
            // This `j` loop should be independent of the `i` loop's `i` state.
            // Simply `break` if an obstacle is hit, otherwise propagate.
            // The specific `if (i==0)` check is wrong here.
            // We correctly initialize dp[0][0] in the very first column initialization loop.
            // We only need to propagate from dp[0][j-1] if j > 0.
            // So, remove the `if (i == 0)` and `else if` for `j == 0` condition.
            // dp[0][0] value is already determined.
            if (dp[0][0] == 0) { // If dp[0][0] is 0, it means grid[0][0] was 1, so the whole first row paths are 0 (and it should break)
                 // This case is implicitly handled because the 'break' will skip all subsequent cells.
                 // If grid[0][0] is 1, then 'i' loop sets dp[0][0] to 0 and breaks.
                 // This 'j' loop will see grid[0][0] == 1, set dp[0][0] to 0 and break.
            }
            // If we are here and j==0, it means grid[0][0] was 0, so dp[0][0] should be 1.
            // This is already handled by the first loop. No action needed for j==0.
        else if dp[0][j-1] == 1 then 
            dp[0][j] := 1;
        else
            dp[0][j] := 0; 
        j := j + 1;
    }
    
    // Compute paths for the rest of the grid
    i := 1; // Start from second row
    while i < m
        invariant 1 <= i <= m
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
        invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
        invariant (forall r :: 1 <= r < i ==> (forall c :: 1 <= c < n ==> dp[r][c] == (if grid[r][c] == 0 then (dp[r-1][c] + dp[r][c-1]) else 0)))
        invariant (forall r :: 1 <= r < i ==> dp[r][0] == (if grid[r][0] == 0 then dp[r-1][0] else 0))
        // Trailing conditions for dp[0][c] are for j loop, not i loop.
        // It's already setup by the previous j loop.
        // For the invariant here, we only need to state what is known about first row:
        invariant (forall c :: 0 <= c < n ==> (dp[0][c] == (if grid[0][c] == 0 then (if c == 0 then 1 else if dp[0][c-1] == 1 then 1 else 0) else 0)))
        // The condition for c==0 for dp[0][c] should be simplified as dp[0][0] is already fixed as 1
        // after the previous initialization blocks if grid[0][0] is 0. 
        // More simply:
        invariant (forall c :: 0 <= c < n ==> (dp[0][c] == (if grid[0][c] == 1 then 0 else (if c == 0 then 1 else dp[0][c-1]))))
    {
        j := 1; // Start from second column
        while j < n
            invariant 1 <= j <= n
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n ==> dp[r][c] >= 0))
            invariant (forall r :: 0 <= r < i ==> (forall c :: 0 <= c < n && grid[r][c] == 1 ==> dp[r][c] == 0))
            invariant (forall r :: 1 <= r < i ==> (forall c :: 1 <= c < n ==> dp[r][c] == (if grid[r][c] == 0 then (dp[r-1][c] + dp[r][c-1]) else 0)))
            invariant (forall c :: 1 <= c < j ==> dp[i][c] == (if grid[i][c] == 0 then (dp[i-1][c] + dp[i][c-1]) else 0))
            invariant dp[i][0] == (if grid[i][0] == 0 then dp[i-1][0] else 0)
            invariant (forall c :: 0 <= c < n ==> (dp[0][c] == (if grid[0][c] == 1 then 0 else (if c == 0 then 1 else dp[0][c-1]))))

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

