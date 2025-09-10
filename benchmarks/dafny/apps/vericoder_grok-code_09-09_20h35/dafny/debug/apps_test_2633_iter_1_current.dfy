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
    var dp := new int[m][];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall k :: 0 <= k < i ==> dp[k] != null && |dp[k]| == n
    {
        dp[i] := new int[n];
        i := i + 1;
    }

    dp[m-1][n-1] := if dungeon[m-1][n-1] >= 0 then 1 else 1 - dungeon[m-1][n-1];
    
    i := m - 1;
    while i >= 0
        invariant -1 <= i <= m-1
        invariant dp[m-1][n-1] == (if dungeon[m-1][n-1] >= 0 then 1 else 1 - dungeon[m-1][n-1])
        invariant forall r,c :: if r == m-1 && c == n-1 then true else (0 <= r < m && 0 <= c < n && dp[r][c] >= 1) && 
                  (forall r',c' :: r' > i || (r' == i && c' > -1) ==> (if r' == m-1 && c' == n-1 then false else if 0 <= r' < m && 0 <= c' < n then dp[r'][c'] >= 1))
    {
        var j := n - 1;
        while j >= 0
            invariant -1 <= j <= n-1
            invariant dp[m-1][n-1] == (if dungeon[m-1][n-1] >= 0 then 1 else 1 - dungeon[m-1][n-1])
            invariant forall r,c :: if r > i || (r == i && c >= j) then (if r == m-1 && c == n-1 then true else if 0 <= r < m && 0 <= c < n then dp[r][c] >= 1)
        {
            if i == m-1 && j == n-1 {
                // already set
            } else {
                var maxNext := (var neg_inf := -2147483648; neg_inf;);
                if i + 1 < m {
                    maxNext := dp[i+1][j];
                }
                if j + 1 < n {
                    if maxNext < dp[i][j+1] {
                        maxNext := dp[i][j+1];
                    }
                }
                dp[i][j] := if maxNext - dungeon[i][j] > 1 then maxNext - dungeon[i][j] else 1;
            }
            j := j - 1;
        }
        i := i - 1;
    }

    result := dp[0][0];
}
// </vc-code>

