predicate ValidInput(n: int, times: seq<int>, T: int)
{
    n >= 1 && |times| == n && T >= 1 && 
    forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
}

function maxStudentsInWindow(times: seq<int>, T: int): int
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
{
    maxStudentsInWindowUpTo(times, T, 1000)
}

function maxStudentsInWindowUpTo(times: seq<int>, T: int, maxStart: int): int
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires maxStart >= 0
    ensures 0 <= maxStudentsInWindowUpTo(times, T, maxStart) <= |times|
{
    if maxStart < 1 then 0
    else
        var count := countStudentsInWindow(times, maxStart, T);
        var restMax := maxStudentsInWindowUpTo(times, T, maxStart - 1);
        if count > restMax then count else restMax
}

function countStudentsInWindow(times: seq<int>, start: int, T: int): int
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires start >= 1
    ensures 0 <= countStudentsInWindow(times, start, T) <= |times|
{
    countStudentsInWindowHelper(times, start, T, 0)
}

function countStudentsInWindowHelper(times: seq<int>, start: int, T: int, index: int): int
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires start >= 1
    requires 0 <= index <= |times|
    ensures 0 <= countStudentsInWindowHelper(times, start, T, index) <= |times| - index
    decreases |times| - index
{
    if index == |times| then 0
    else
        var countRest := countStudentsInWindowHelper(times, start, T, index + 1);
        if start <= times[index] <= start + T - 1 then countRest + 1 else countRest
}

// <vc-helpers>
lemma maxStudentsInWindowCorrectness(times: seq<int>, T: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    ensures maxStudentsInWindow(times, T) == maxStudentsInWindowUpTo(times, T, 1000)
{
}

lemma maxStudentsInWindowUpToBound(times: seq<int>, T: int, maxStart: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires maxStart >= 0
    ensures 0 <= maxStudentsInWindowUpTo(times, T, maxStart) <= |times|
{
}

lemma countStudentsInWindowBound(times: seq<int>, start: int, T: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires start >= 1
    ensures 0 <= countStudentsInWindow(times, start, T) <= |times|
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, times: seq<int>, T: int) returns (result: int)
    requires ValidInput(n, times, T)
    ensures result >= 0
    ensures result <= n
    ensures result == maxStudentsInWindow(times, T)
// </vc-spec>
// <vc-code>
{
    var maxCount := 0;
    var start := 1;
    
    while start <= 1000
        invariant 1 <= start <= 1001
        invariant 0 <= maxCount <= n
        invariant maxCount == maxStudentsInWindowUpTo(times, T, start - 1)
    {
        var count := 0;
        var i := 0;
        
        while i < n
            invariant 0 <= i <= n
            invariant 0 <= count <= i
            invariant count == countStudentsInWindowHelper(times, start, T, 0) - countStudentsInWindowHelper(times, start, T, i)
        {
            if start <= times[i] <= start + T - 1 {
                count := count + 1;
            }
            i := i + 1;
        }
        
        assert count == countStudentsInWindow(times, start, T);
        
        if count > maxCount {
            maxCount := count;
        }
        
        start := start + 1;
    }
    
    result := maxCount;
}
// </vc-code>

