Find the minimum initial health required for a character to travel from the top-left 
corner to the bottom-right corner of an M x N grid. The character can only move right 
or down, and dies if health drops to 0 or below at any point.

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

method calculateMinimumHP(dungeon: seq<seq<int>>) returns (result: int)
    requires ValidDungeon(dungeon)
    ensures result >= 1
{
    var row := |dungeon|;
    var col := |dungeon[0]|;

    // Initialize dp array
    var dp := new int[row, col];

    // Initialize bottom-right corner
    if dungeon[row-1][col-1] <= 0 {
        dp[row-1, col-1] := -dungeon[row-1][col-1] + 1;
    } else {
        dp[row-1, col-1] := 1;
    }
    assert dp[row-1, col-1] >= 1;

    // Fill rightmost column
    var r := row - 2;
    while r >= 0
        invariant -1 <= r < row - 1
        invariant forall i :: r + 1 <= i < row ==> dp[i, col-1] >= 1
    {
        dp[r, col-1] := dp[r+1, col-1] - dungeon[r][col-1];
        if dp[r, col-1] <= 0 {
            dp[r, col-1] := 1;
        }
        assert dp[r, col-1] >= 1;
        r := r - 1;
    }

    // Assert that all rightmost column entries are >= 1
    assert forall i :: 0 <= i < row ==> dp[i, col-1] >= 1;

    // Fill bottom row
    var c := col - 2;
    while c >= 0
        invariant -1 <= c < col - 1
        invariant forall j :: c + 1 <= j < col ==> dp[row-1, j] >= 1
        invariant forall i :: 0 <= i < row ==> dp[i, col-1] >= 1
    {
        dp[row-1, c] := dp[row-1, c+1] - dungeon[row-1][c];
        if dp[row-1, c] <= 0 {
            dp[row-1, c] := 1;
        }
        assert dp[row-1, c] >= 1;
        c := c - 1;
    }

    // Fill the rest of the dp table
    r := row - 2;
    while r >= 0
        invariant -1 <= r < row - 1
        invariant forall i :: r + 1 <= i < row ==> forall j :: 0 <= j < col ==> dp[i, j] >= 1
        invariant forall j :: 0 <= j < col ==> dp[row-1, j] >= 1
        invariant forall i :: 0 <= i < row ==> dp[i, col-1] >= 1
    {
        c := col - 2;
        while c >= 0
            invariant -1 <= c < col - 1
            invariant forall j :: c + 1 <= j < col ==> dp[r, j] >= 1
            invariant forall i :: r + 1 <= i < row ==> forall j :: 0 <= j < col ==> dp[i, j] >= 1
            invariant forall j :: 0 <= j < col ==> dp[row-1, j] >= 1
            invariant forall i :: 0 <= i < row ==> dp[i, col-1] >= 1
        {
            var minNext := if dp[r+1, c] < dp[r, c+1] then dp[r+1, c] else dp[r, c+1];
            dp[r, c] := minNext - dungeon[r][c];
            if dp[r, c] <= 0 {
                dp[r, c] := 1;
            }
            assert dp[r, c] >= 1;
            c := c - 1;
        }
        r := r - 1;
    }

    result := dp[0, 0];
    assert result >= 1;
}
