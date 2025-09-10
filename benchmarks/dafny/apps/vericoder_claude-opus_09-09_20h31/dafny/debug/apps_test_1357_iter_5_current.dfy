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
    ensures 0 <= MinTimeToComplete(n, tasks, currentPos, taskIndex) <= n - 1
{
    var target := tasks[taskIndex];
    if target >= currentPos {
        assert MinTimeToComplete(n, tasks, currentPos, taskIndex) == target - currentPos;
        assert 0 <= target - currentPos <= n - currentPos;
        assert target - currentPos <= n - 1;
    } else {
        assert MinTimeToComplete(n, tasks, currentPos, taskIndex) == (n - currentPos) + target;
        assert target < currentPos;
        assert 1 <= target < currentPos <= n;
        assert currentPos > 1;  // since target >= 1 and target < currentPos
        if currentPos == n {
            // If currentPos == n and target < n, then we wrap around
            assert n - currentPos == 0;
            assert MinTimeToComplete(n, tasks, currentPos, taskIndex) == 0 + target == target;
            assert target <= n - 1;
        } else {
            assert currentPos < n;
            assert (n - currentPos) >= 1;
            assert target >= 1;
            assert (n - currentPos) + target >= 2;
            assert (n - currentPos) + target == n - (currentPos - target);
            assert currentPos - target >= 1;
            assert n - (currentPos - target) <= n - 1;
        }
    }
}

lemma FirstTaskTime(n: int, tasks: seq<int>)
    requires n >= 2
    requires |tasks| >= 1
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    ensures MinTimeToComplete(n, tasks, 1, 0) == tasks[0] - 1
{
    var target := tasks[0];
    assert 1 <= target <= n;
    if target >= 1 {
        assert MinTimeToComplete(n, tasks, 1, 0) == target - 1;
    }
}

lemma TotalTimeBound(n: int, m: int, tasks: seq<int>, totalTime: int)
    requires n >= 2 && m >= 1
    requires |tasks| == m
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires totalTime <= m * (n - 1)
    requires 1 <= tasks[m-1] <= n
    ensures totalTime <= (m - 1) * n + tasks[m-1] - 1
{
    calc <= {
        totalTime;
        m * (n - 1);
        m * n - m;
        { assert m * n - m == (m - 1) * n + n - m; }
        (m - 1) * n + n - m;
        { assert m >= 1; assert n - m <= n - 1; }
        (m - 1) * n + n - 1;
        { assert tasks[m-1] <= n; assert n - 1 == n + tasks[m-1] - 1 - tasks[m-1]; }
        (m - 1) * n + n + tasks[m-1] - 1 - tasks[m-1];
        { assert n - tasks[m-1] >= 0; }
        (m - 1) * n + tasks[m-1] - 1 + (n - tasks[m-1]);
        { assert n - tasks[m-1] >= 0; }
        (m - 1) * n + tasks[m-1] - 1;
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
        invariant i > 0 ==> totalTime >= tasks[i-1] - 1
        invariant i == 0 ==> currentPos == 1
        invariant i == 0 ==> totalTime == 0
        invariant totalTime <= i * (n - 1)
    {
        var timeToTask := MinTimeToComplete(n, tasks, currentPos, i);
        MinTimeProperties(n, tasks, currentPos, i);
        
        if i == 0 {
            FirstTaskTime(n, tasks);
            assert timeToTask == tasks[0] - 1;
        }
        
        totalTime := totalTime + timeToTask;
        currentPos := tasks[i];
        i := i + 1;
        
        assert timeToTask <= n - 1;
        assert totalTime <= (i - 1) * (n - 1) + (n - 1);
        assert totalTime <= i * (n - 1);
    }
    
    assert i == m;
    assert m > 0;
    assert currentPos == tasks[m-1];
    assert totalTime >= tasks[m-1] - 1;
    assert totalTime <= m * (n - 1);
    
    TotalTimeBound(n, m, tasks, totalTime);
    assert totalTime <= (m - 1) * n + tasks[m-1] - 1;
    
    return totalTime;
}
// </vc-code>

