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
lemma maxStudentsInWindowUpToMonotonic(times: seq<int>, T: int, m1: int, m2: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires 0 <= m1 <= m2
    ensures maxStudentsInWindowUpTo(times, T, m1) <= maxStudentsInWindowUpTo(times, T, m2)
{
    if m1 < 1 {
        assert maxStudentsInWindowUpTo(times, T, m1) == 0;
    } else if m1 == m2 {
        // Base case: equal
    } else {
        // m1 < m2
        maxStudentsInWindowUpToMonotonic(times, T, m1, m2 - 1);
        var count := countStudentsInWindow(times, m2, T);
        var restMax := maxStudentsInWindowUpTo(times, T, m2 - 1);
        assert maxStudentsInWindowUpTo(times, T, m2) == (if count > restMax then count else restMax);
        assert maxStudentsInWindowUpTo(times, T, m2) >= restMax;
        assert restMax >= maxStudentsInWindowUpTo(times, T, m1);
    }
}

lemma maxStudentsCorrectness(times: seq<int>, T: int, start: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires 1 <= start <= 1000
    requires forall s :: 1 <= s < start ==> countStudentsInWindow(times, s, T) <= maxStudentsInWindowUpTo(times, T, start - 1)
    ensures countStudentsInWindow(times, start, T) <= maxStudentsInWindowUpTo(times, T, start)
{
    var count := countStudentsInWindow(times, start, T);
    var restMax := maxStudentsInWindowUpTo(times, T, start - 1);
    assert maxStudentsInWindowUpTo(times, T, start) == (if count > restMax then count else restMax);
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
        invariant maxCount == maxStudentsInWindowUpTo(times, T, start - 1)
    {
        var count := 0;
        var i := 0;
        
        while i < n
            invariant 0 <= i <= n
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
        
        assert maxCount == maxStudentsInWindowUpTo(times, T, start);
        start := start + 1;
    }
    
    assert start == 1001;
    assert maxCount == maxStudentsInWindowUpTo(times, T, 1000);
    result := maxCount;
}
// </vc-code>

