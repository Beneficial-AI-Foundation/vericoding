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
lemma HealthMonotonic(dungeon: seq<seq<int>>, path: seq<(int, int)>, initialHealth: int, step: int)
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= step < |path|
    requires initialHealth >= 1
    ensures healthAtStep(dungeon, path, step, initialHealth) >= healthAtStep(dungeon, path, step, 1)
{
    if step > 0 {
        HealthMonotonic(dungeon, path, initialHealth, step-1);
    }
}

lemma HealthAdditive(dungeon: seq<seq<int>>, path: seq<(int, int)>, step: int, h1: int, h2: int)
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= step < |path|
    requires h1 >= 0
    ensures healthAtStep(dungeon, path, step, h1 + h2) == healthAtStep(dungeon, path, step, h2) + h1
{
    if step > 0 {
        HealthAdditive(dungeon, path, step-1, h1, h2);
    }
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
    var dp : array2<int> := new int[m, n];
    
    dp[m-1, n-1] := max(1 - dungeon[m-1][n-1], 1);
    
    var i := m-1;
    var j := n-2;
    while j >= 0
        decreases n-1 - j
    {
        dp[i, j] := max(dp[i, j+1] - dungeon[i][j], 1);
        j := j - 1;
    }
    
    i := m-2;
    while i >= 0
        decreases m-1 - i
    {
        j := n-1;
        while j >= 0
            decreases n-1 - j
        {
            var right := if j < n-1 then dp[i, j+1] else int.MaxValue;
            var down := if i < m-1 then dp[i+1, j] else int.MaxValue;
            var minNeighbor := min(right, down);
            dp[i, j] := max(minNeighbor - dungeon[i][j], 1);
            j := j - 1;
        }
        i := i - 1;
    }
    
    result := dp[0, 0];
}
// </vc-code>

