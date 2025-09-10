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
lemma MinTimeToCompleteNonNegative(n: int, tasks: seq<int>, currentPos: int, taskIndex: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
    ensures MinTimeToComplete(n, tasks, currentPos, taskIndex) >= 0
{
    var target := tasks[taskIndex];
    if target >= currentPos {
        assert target - currentPos >= 0;
    } else {
        assert (n - currentPos) + target >= 0;
    }
}

lemma MinTimeToCompleteBound(n: int, tasks: seq<int>, currentPos: int, taskIndex: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
    ensures MinTimeToComplete(n, tasks, currentPos, taskIndex) <= n - 1
{
    var target := tasks[taskIndex];
    if target >= currentPos {
        assert target - currentPos <= n - 1;
    } else {
        assert (n - currentPos) + target <= n - 1;
    }
}

lemma TotalTimeBound(n: int, m: int, tasks: seq<int>, totalTime: int, pos: int)
    requires ValidInput(n, m, tasks)
    requires m > 0
    requires totalTime >= 0
    requires totalTime <= (m - 1) * n
    requires 1 <= pos <= n
    ensures totalTime + tasks[m-1] - 1 <= (m - 1) * n + tasks[m-1] - 1
{
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
    if m == 0 {
        return 0;
    }
    
    var totalTime := 0;
    var currentPos := 1;
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant totalTime >= 0
        invariant 1 <= currentPos <= n
        invariant i > 0 ==> totalTime >= tasks[i-1] - 1
        invariant totalTime <= i * n
    {
        MinTimeToCompleteNonNegative(n, tasks, currentPos, i);
        MinTimeToCompleteBound(n, tasks, currentPos, i);
        
        var timeToMove := MinTimeToComplete(n, tasks, currentPos, i);
        totalTime := totalTime + timeToMove;
        currentPos := tasks[i];
        i := i + 1;
    }
    
    TotalTimeBound(n, m, tasks, totalTime - (tasks[m-1] - 1), currentPos);
    result := totalTime;
}
// </vc-code>

