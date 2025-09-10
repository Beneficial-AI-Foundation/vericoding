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
function max(a: int, b: int): int {
    if a > b then a else b
}

function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method calculateMinimumHP(dungeon: seq<seq<int>>) returns (result: int)
    requires ValidDungeon(dungeon)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    var rows := |dungeon|;
    var cols := |dungeon[0]|;
    var dp: array2<int>;
    dp := new array2<int>(rows, cols); // Initialize with default values (0 for int)

    // Initialize the bottom-right cell
    dp[rows - 1, cols - 1] := max(1, 1 - dungeon[rows - 1][cols - 1]);

    // Initialize the last row (moving right to left)
    for c := cols - 2 downto 0 {
        dp[rows - 1, c] := max(1, dp[rows - 1, c + 1] - dungeon[rows - 1][c]);
    }

    // Initialize the last column (moving bottom to top)
    for r := rows - 2 downto 0 {
        dp[r, cols - 1] := max(1, dp[r + 1, cols - 1] - dungeon[r][cols - 1]);
    }

    // Fill the rest of the DP table
    for r := rows - 2 downto 0 {
        for c := cols - 2 downto 0 {
            var min_health_needed_from_next_room := min(dp[r + 1, c], dp[r, c + 1]);
            dp[r, c] := max(1, min_health_needed_from_next_room - dungeon[r][c]);
        }
    }

    return dp[0, 0];
}
// </vc-code>

