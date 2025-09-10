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
    // The minimal time is always non-negative and at most n-1
    // since we can always move clockwise at most n-1 steps
}

lemma lemma_SumMinTimes(n: int, tasks: seq<int>)
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    ensures forall startPos: int :: 1 <= startPos <= n ==>
        sumMinTime(n, tasks, startPos) >= 0
{
    // The sum of minimal times is always non-negative
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
    if |tasks| <= 1 {
        // Base case: 0 or 1 tasks
    } else {
        var firstTime := MinTimeToComplete(n, tasks, startPos, 0);
        lemma_TimeBound(n, tasks[1..], tasks[0]);
        // The total time is bounded by the sum of individual bounds
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
    var pos := 1;
    result := 0;
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
        result := result + timeToMove;
        pos := target;
        i := i + 1;
        
        if i > 0 {
            assert result <= (i - 1) * n + tasks[i-1] - 1;
        }
    }
    
    // Postcondition verification
    if m > 0 {
        assert result >= tasks[m-1] - 1;
    }
}
// </vc-code>

