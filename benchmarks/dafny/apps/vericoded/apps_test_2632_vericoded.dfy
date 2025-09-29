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
function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma PathSumNonNegative(path: seq<(int, int)>, grid: array2<int>)
    requires ValidInput(grid)
    requires forall i :: 0 <= i < |path| ==> 0 <= path[i].0 < grid.Length0 && 0 <= path[i].1 < grid.Length1
    ensures PathSum(path, grid) >= 0
    decreases |path|
{
    if |path| == 0 {
        // Base case: empty path has sum 0
    } else {
        // Inductive case: grid[path[0].0, path[0].1] >= 0 by ValidInput
        // and PathSum(path[1..], grid) >= 0 by induction
        PathSumNonNegative(path[1..], grid);
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
    
    // Initialize first cell
    dp[0, 0] := grid[0, 0];
    
    // Initialize first row (can only come from left)
    var j := 1;
    while j < n
        invariant 1 <= j <= n
        invariant dp[0, 0] == grid[0, 0]
        invariant forall k :: 0 <= k < j ==> dp[0, k] >= 0
        invariant forall k :: 1 <= k < j ==> dp[0, k] == dp[0, k-1] + grid[0, k]
    {
        dp[0, j] := dp[0, j-1] + grid[0, j];
        j := j + 1;
    }
    
    // Initialize first column (can only come from above)
    var i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant dp[0, 0] == grid[0, 0]
        invariant forall k :: 0 <= k < n ==> dp[0, k] >= 0
        invariant forall k :: 1 <= k < n ==> dp[0, k] == dp[0, k-1] + grid[0, k]
        invariant forall k :: 0 <= k < i ==> dp[k, 0] >= 0
        invariant forall k :: 1 <= k < i ==> dp[k, 0] == dp[k-1, 0] + grid[k, 0]
    {
        dp[i, 0] := dp[i-1, 0] + grid[i, 0];
        i := i + 1;
    }
    
    // Fill the rest of the dp table
    i := 1;
    while i < m
        invariant 1 <= i <= m
        invariant dp[0, 0] == grid[0, 0]
        invariant forall c :: 0 <= c < n ==> dp[0, c] >= 0
        invariant forall c :: 1 <= c < n ==> dp[0, c] == dp[0, c-1] + grid[0, c]
        invariant forall r :: 0 <= r < m ==> dp[r, 0] >= 0
        invariant forall r :: 1 <= r < m ==> dp[r, 0] == dp[r-1, 0] + grid[r, 0]
        invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> dp[r, c] >= 0
        invariant forall r, c :: 0 < r < i && 0 < c < n ==> 
            dp[r, c] == min(dp[r-1, c], dp[r, c-1]) + grid[r, c]
    {
        j := 1;
        while j < n
            invariant 1 <= j <= n
            invariant dp[0, 0] == grid[0, 0]
            invariant forall c :: 0 <= c < n ==> dp[0, c] >= 0
            invariant forall c :: 1 <= c < n ==> dp[0, c] == dp[0, c-1] + grid[0, c]
            invariant forall r :: 0 <= r < m ==> dp[r, 0] >= 0
            invariant forall r :: 1 <= r < m ==> dp[r, 0] == dp[r-1, 0] + grid[r, 0]
            invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> dp[r, c] >= 0
            invariant forall c :: 0 <= c < j ==> dp[i, c] >= 0
            invariant forall c :: 1 <= c < j ==> dp[i, c] == min(dp[i-1, c], dp[i, c-1]) + grid[i, c]
            invariant forall r, c :: 0 < r < i && 0 < c < n ==> 
                dp[r, c] == min(dp[r-1, c], dp[r, c-1]) + grid[r, c]
        {
            var fromUp := dp[i-1, j];
            var fromLeft := dp[i, j-1];
            dp[i, j] := min(fromUp, fromLeft) + grid[i, j];
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := dp[m-1, n-1];
}
// </vc-code>

