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
function max(a: int, b: int): int { if a >= b then a else b }
function min(a: int, b: int): int { if a <= b then a else b }
function dpValue(dungeon: seq<seq<int>>, i: int, j: int): (value: int)
    requires ValidDungeon(dungeon)
    requires 0 <= i < |dungeon| && 0 <= j < |dungeon[0]|
    decreases (|dungeon| - i) + (|dungeon[0]| - j)
{
    if i == |dungeon|-1 && j == |dungeon[0]|-1 then
        max(1, 1 - dungeon[i][j])
    else if i == |dungeon|-1 then
        max(1, dpValue(dungeon, i, j+1) - dungeon[i][j])
    else if j == |dungeon[0]|-1 then
        max(1, dpValue(dungeon, i+1, j) - dungeon[i][j])
    else
        max(1, min(dpValue(dungeon, i+1, j), dpValue(dungeon, i, j+1)) - dungeon[i][j])
}
// </vc-helpers>

// <vc-spec>
method calculateMinimumHP(dungeon: seq<seq<int>>) returns (result: int)
    requires ValidDungeon(dungeon)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    return dpValue(dungeon, 0, 0);
}
// </vc-code>

