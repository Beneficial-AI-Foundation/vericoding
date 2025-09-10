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
lemma lemma_MinTimeProperties(n: int, tasks: seq<int>, currentPos: int, taskIndex: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
    ensures MinTimeToComplete(n, tasks, currentPos, taskIndex) >= 0
    ensures MinTimeToComplete(n, tasks, currentPos, taskIndex) <= n - 1
{
}

lemma lemma_SumMinTimes(n: int, tasks: seq<int>)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    ensures forall startPos: int :: 1 <= startPos <= n ==>
        sumMinTime(n, tasks, startPos) >= 0
{
}

ghost function sumMinTime(n: int, tasks: seq<int>, startPos: int): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= startPos <= n
    decreases |tasks|
{
    if |tasks| == 0 then 0
    else
        var firstTime := MinTimeToComplete(n, tasks, startPos, 0);
        firstTime + sumMinTime(n, tasks[1..], tasks[0])
}

lemma lemma_TimeBound(n: int, tasks: seq<int>, startPos: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= startPos <= n
    ensures sumMinTime(n, tasks, startPos) <= (|tasks| - 1) * n + tasks[|tasks| - 1] - 1
    decreases |tasks|
{
    if |tasks| == 0 {
    } else if |tasks| == 1 {
        assert sumMinTime(n, tasks, startPos) == MinTimeToComplete(n, tasks, startPos, 0);
        lemma_MinTimeProperties(n, tasks, startPos, 0);
    } else {
        var firstTime := MinTimeToComplete(n, tasks, startPos, 0);
        lemma_MinTimeProperties(n, tasks, startPos, 0);
        
        var restTasks := tasks[1..];
        lemma_TimeBound(n, restTasks, tasks[0]);
        
        var restBound := (|restTasks| - 1) * n + restTasks[|restTasks| - 1] - 1;
        var total := firstTime + restBound;
        
        assert sumMinTime(n, tasks, startPos) == firstTime + sumMinTime(n, restTasks, tasks[0]);
        assert sumMinTime(n, restTasks, tasks[0]) <= restBound;
    }
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
    result := 0;
    var pos := 1;
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant 1 <= pos <= n
        invariant result >= 0
        invariant result == sumMinTime(n, tasks[0..i], 1)
        invariant i > 0 ==> result <= (i - 1) * n + tasks[i-1] - 1
    {
        var target := tasks[i];
        var timeToMove := MinTimeToComplete(n, tasks, pos, i);
        lemma_MinTimeProperties(n, tasks, pos, i);
        result := result + timeToMove;
        pos := target;
        i := i + 1;
        
        if i > 0 {
            lemma_TimeBound(n, tasks[0..i], 1);
        }
    }
}
// </vc-code>

