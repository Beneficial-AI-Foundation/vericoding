predicate ValidInput(n: int, m: int, tasks: seq<int>)
{
    n >= 2 && m >= 1 && |tasks| == m && 
    forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
}

function MinTimeToComplete(n: int, tasks: seq<int>, currentPos: int, taskIndex: int): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
{
    var target := tasks[taskIndex];
    if target >= currentPos then target - currentPos
    else (n - currentPos) + target
}

// <vc-helpers>
function Max(a: int, b: int): int {
    if a > b then a else b
}

function sumMinTimeToComplete(n: int, tasks: seq<int>, count: int): int
    requires 0 <= count <= |tasks|
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
{
    if count == 0 then 0
    else sumMinTimeToComplete(n, tasks, count - 1) + MinTimeToComplete(n, tasks, if count - 1 == 0 then 1 else tasks[count - 2], count - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, tasks: seq<int>) returns (result: int)
    requires ValidInput(n, m, tasks)
    ensures result >= 0
    ensures m > 0 ==> result >= tasks[m-1] - 1
    ensures result <= (m - 1) * n + tasks[m-1] - 1
// </vc-spec>
// <vc-code>
{
    var maxTime := 0;
    var currentPos := 1;

    for i := 0 to m - 1
        invariant 0 <= i <= m
        invariant maxTime >= 0
        invariant 1 <= currentPos <= n
        invariant forall k :: 0 <= k < i ==> 1 <= tasks[k] <= n
        invariant i == 0 ==> maxTime == 0 && currentPos == 1
        invariant i > 0 ==> currentPos == tasks[i-1]
        invariant i > 0 ==> maxTime >= tasks[i-1] - 1
        invariant i > 0 ==> maxTime == sumMinTimeToComplete(n, tasks, i)
    {
        var target := tasks[i];
        var timeToMove: int;

        if target >= currentPos then
            timeToMove := target - currentPos;
        else
            timeToMove := (n - currentPos) + target;

        maxTime := maxTime + timeToMove;
        currentPos := target;
    }
    result := maxTime;
}
// </vc-code>

