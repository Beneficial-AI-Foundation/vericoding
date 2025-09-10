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

function sumDungeonValues(dungeon: seq<seq<int>>, path: seq<(int, int)>, start: int, end: int): int
    requires ValidDungeon(dungeon)
    requires isValidPath(dungeon, path)
    requires 0 <= start <= end < |path|
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
    var path := [(0, 0)];
    var r := 0;
    var c := 0;
    while r < rows - 1 || c < cols - 1
        decreases (rows - 1 - r) + (cols - 1 - c)
    {
        if r < rows - 1 {
            r := r + 1;
            path := path + [(r, c)];
        } else {
            c := c + 1;
            path := path + [(r, c)];
        }
    }
    path
}

lemma RightDownPathIsValid(dungeon: seq<seq<int>>)
    requires ValidDungeon(dungeon)
    ensures isValidPath(dungeon, rightDownPath(|dungeon|, |dungeon[0]|))
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
    var path := rightDownPath(rows, cols);
    
    RightDownPathIsValid(dungeon);
    
    var minHealth := 1;
    var i := 0;
    
    while i < |path|
        invariant 0 <= i <= |path|
        invariant minHealth >= 1
    {
        var (r, c) := path[i];
        var health := healthAtStep(dungeon, path, i, minHealth);
        
        if health <= 0 {
            minHealth := minHealth + (1 - health);
        }
        
        i := i + 1;
    }
    
    result := minHealth;
}
// </vc-code>

