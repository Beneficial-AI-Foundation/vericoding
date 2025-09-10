predicate ValidDungeon(dungeon: seq<seq<int>>)
{
    |dungeon| > 0 &&
    (forall i :: 0 <= i < |dungeon| ==> |dungeon[i]| > 0) &&
    (forall i :: 0 <= i < |dungeon| ==> |dungeon[i]| == |dungeon[0]|)
}

predicate isValidPath(dungeon: seq<seq<int>>, path: seq<(int, int)>)
    requires ValidDungeon(dungeon)
{
    |path| > 0 &&
    path[0] == (0, 0) &&
    path[|path|-1] == (|dungeon|-1, |dungeon[0]|-1) &&
    (forall i :: 0 <= i < |path| ==> 
        var (r, c) := path[i];
        0 <= r < |dungeon| && 0 <= c < |dungeon[0]|) &&
    forall i :: 0 <= i < |path|-1 ==> 
        (path[i].1 == path[i+1].1 && path[i].0 + 1 == path[i+1].0) ||
        (path[i].0 == path[i+1].0 && path[i].1 + 1 == path[i+1].1)
}

function healthAtStep(dungeon: seq<seq<int>>, path: seq<(int, int)>, step: int, initialHealth: int): int
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= step < |path|
    decreases step
{
    if step == 0 then 
        var (r, c) := path[0];
        initialHealth + dungeon[r][c]
    else
        var (r, c) := path[step];
        healthAtStep(dungeon, path, step-1, initialHealth) + dungeon[r][c]
}

predicate canSurvivePath(dungeon: seq<seq<int>>, path: seq<(int, int)>, initialHealth: int)
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
{
    forall i :: 0 <= i < |path| ==> 
        healthAtStep(dungeon, path, i, initialHealth) > 0
}

// <vc-helpers>
function min(a: int, b: int): int
{
    if a <= b then a else b
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method calculateMinimumHP(dungeon: seq<seq<int>>) returns (result: int)
    requires ValidDungeon(dungeon)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    var m := |dungeon|;
    var n := |dungeon[0]|;
    
    // Create a 2D array to store minimum health required at each position
    var dp := new int[m, n];
    
    // Start from the destination (bottom-right)
    // The minimum health needed after leaving the last cell must be at least 1
    dp[m-1, n-1] := max(1, 1 - dungeon[m-1][n-1]);
    
    // Fill the last column (can only move down)
    var i := m - 2;
    while i >= 0
        invariant -1 <= i < m - 1
    {
        dp[i, n-1] := max(1, dp[i+1, n-1] - dungeon[i][n-1]);
        i := i - 1;
    }
    
    // Fill the last row (can only move right)
    var j := n - 2;
    while j >= 0
        invariant -1 <= j < n - 1
    {
        dp[m-1, j] := max(1, dp[m-1, j+1] - dungeon[m-1][j]);
        j := j - 1;
    }
    
    // Fill the rest of the table
    i := m - 2;
    while i >= 0
        invariant -1 <= i < m - 1
    {
        j := n - 2;
        while j >= 0
            invariant -1 <= j < n - 1
        {
            // Minimum health needed if going right or down
            var minHealthFromRight := max(1, dp[i, j+1] - dungeon[i][j]);
            var minHealthFromDown := max(1, dp[i+1, j] - dungeon[i][j]);
            
            // Take the minimum of the two options
            dp[i, j] := min(minHealthFromRight, minHealthFromDown);
            
            j := j - 1;
        }
        i := i - 1;
    }
    
    result := dp[0, 0];
}
// </vc-code>

