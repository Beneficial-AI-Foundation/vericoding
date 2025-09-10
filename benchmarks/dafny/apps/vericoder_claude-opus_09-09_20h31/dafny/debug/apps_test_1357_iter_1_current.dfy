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
lemma MinTimeProperties(n: int, tasks: seq<int>, currentPos: int, taskIndex: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
    ensures 0 <= MinTimeToComplete(n, tasks, currentPos, taskIndex) < n
{
    var target := tasks[taskIndex];
    if target >= currentPos {
        assert MinTimeToComplete(n, tasks, currentPos, taskIndex) == target - currentPos;
        assert target - currentPos >= 0;
        assert target - currentPos <= n - 1;
    } else {
        assert MinTimeToComplete(n, tasks, currentPos, taskIndex) == (n - currentPos) + target;
        assert (n - currentPos) + target >= 1;
        assert (n - currentPos) + target <= n - 1 + target;
        assert (n - currentPos) + target < n;
    }
}

lemma TotalTimeBounds(n: int, tasks: seq<int>, totalTime: int, processed: int)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 0 <= processed <= |tasks|
    requires totalTime >= 0
    ensures processed == |tasks| && |tasks| > 0 ==> totalTime >= tasks[|tasks|-1] - 1
{
    // This follows from the fact that we start at position 1 and need to reach at least tasks[|tasks|-1]
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
        invariant 1 <= currentPos <= n
        invariant totalTime >= 0
        invariant i > 0 ==> currentPos == tasks[i-1]
        invariant totalTime <= i * n
    {
        var timeToTask := MinTimeToComplete(n, tasks, currentPos, i);
        MinTimeProperties(n, tasks, currentPos, i);
        totalTime := totalTime + timeToTask;
        currentPos := tasks[i];
        i := i + 1;
    }
    
    assert i == m;
    assert currentPos == tasks[m-1];
    assert totalTime >= tasks[m-1] - 1;
    assert totalTime <= m * n;
    
    return totalTime;
}
// </vc-code>

