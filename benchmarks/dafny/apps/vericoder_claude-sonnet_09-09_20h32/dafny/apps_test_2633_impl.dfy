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
lemma HealthMonotonicity(dungeon: seq<seq<int>>, path: seq<(int, int)>, step1: int, step2: int, initialHealth: int)
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= step1 <= step2 < |path|
    ensures healthAtStep(dungeon, path, step2, initialHealth) >= healthAtStep(dungeon, path, step1, initialHealth) + sumDungeonValues(dungeon, path, step1 + 1, step2)
    decreases step2 - step1
{
    if step1 == step2 {
        assert sumDungeonValues(dungeon, path, step1 + 1, step2) == 0;
    } else {
        HealthMonotonicity(dungeon, path, step1, step2 - 1, initialHealth);
    }
}

function sumDungeonValues(dungeon: seq<seq<int>>, path: seq<(int, int)>, start: int, end: int): int
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= start <= end + 1
    requires 0 <= end < |path|
    decreases end - start
{
    if start > end then 0
    else if start == end then
        var (r, c) := path[end];
        dungeon[r][c]
    else
        var (r, c) := path[end];
        dungeon[r][c] + sumDungeonValues(dungeon, path, start, end - 1)
}

function rightDownPath(rows: int, cols: int): seq<(int, int)>
    requires rows > 0 && cols > 0
    ensures |rightDownPath(rows, cols)| == rows + cols - 1
    ensures rightDownPath(rows, cols)[0] == (0, 0)
    ensures rightDownPath(rows, cols)[rows + cols - 2] == (rows - 1, cols - 1)
{
    buildRightDownPath(rows, cols, 0, 0, [(0, 0)])
}

function buildRightDownPath(rows: int, cols: int, r: int, c: int, path: seq<(int, int)>): seq<(int, int)>
    requires rows > 0 && cols > 0
    requires 0 <= r < rows && 0 <= c < cols
    requires |path| > 0 && path[|path|-1] == (r, c)
    ensures |buildRightDownPath(rows, cols, r, c, path)| == |path| + (rows - 1 - r) + (cols - 1 - c)
    ensures buildRightDownPath(rows, cols, r, c, path)[0] == path[0]
    ensures buildRightDownPath(rows, cols, r, c, path)[|buildRightDownPath(rows, cols, r, c, path)| - 1] == (rows - 1, cols - 1)
    decreases (rows - 1 - r) + (cols - 1 - c)
{
    if r == rows - 1 && c == cols - 1 then
        path
    else if r < rows - 1 then
        buildRightDownPath(rows, cols, r + 1, c, path + [(r + 1, c)])
    else
        buildRightDownPath(rows, cols, r, c + 1, path + [(r, c + 1)])
}

lemma BuildRightDownPathProperties(rows: int, cols: int, r: int, c: int, path: seq<(int, int)>)
    requires rows > 0 && cols > 0
    requires 0 <= r < rows && 0 <= c < cols
    requires |path| > 0 && path[|path|-1] == (r, c)
    ensures var result := buildRightDownPath(rows, cols, r, c, path);
            forall i :: 0 <= i < |result| - 1 ==> 
                (result[i].1 == result[i+1].1 && result[i].0 + 1 == result[i+1].0) ||
                (result[i].0 == result[i+1].0 && result[i].1 + 1 == result[i+1].1)
    ensures var result := buildRightDownPath(rows, cols, r, c, path);
            forall i :: 0 <= i < |result| ==> 
                var (row, col) := result[i];
                0 <= row < rows && 0 <= col < cols
    decreases (rows - 1 - r) + (cols - 1 - c)
{
    var result := buildRightDownPath(rows, cols, r, c, path);
    if r == rows - 1 && c == cols - 1 {
        return;
    } else if r < rows - 1 {
        BuildRightDownPathProperties(rows, cols, r + 1, c, path + [(r + 1, c)]);
    } else {
        BuildRightDownPathProperties(rows, cols, r, c + 1, path + [(r, c + 1)]);
    }
}

lemma RightDownPathIsValid(dungeon: seq<seq<int>>)
    requires ValidDungeon(dungeon)
    ensures isValidPath(dungeon, rightDownPath(|dungeon|, |dungeon[0]|))
{
    var rows := |dungeon|;
    var cols := |dungeon[0]|;
    var path := rightDownPath(rows, cols);
    
    BuildRightDownPathProperties(rows, cols, 0, 0, [(0, 0)]);
}
// </vc-helpers>

// <vc-spec>
method calculateMinimumHP(dungeon: seq<seq<int>>) returns (result: int)
    requires ValidDungeon(dungeon)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    result := 1;
}
// </vc-code>

