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
lemma maxStudentsInWindowUpToLemma(times: seq<int>, T: int, maxStart: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    requires maxStart >= 0
    ensures maxStart >= 1 ==> maxStudentsInWindowUpTo(times, T, maxStart) >= maxStudentsInWindowUpTo(times, T, maxStart - 1)
{
    if maxStart >= 1 {
        var count := countStudentsInWindow(times, maxStart, T);
        var restMax := maxStudentsInWindowUpTo(times, T, maxStart - 1);
        // The function definition shows that maxStudentsInWindowUpTo returns the maximum of count and restMax
        // Therefore, it must be >= restMax
    }
}

lemma maxStudentsInWindowIsMaximum(times: seq<int>, T: int)
    requires T >= 1
    requires forall i :: 0 <= i < |times| ==> 1 <= times[i] <= 1000
    ensures maxStudentsInWindow(times, T) == maxStudentsInWindowUpTo(times, T, 1000)
{
}

lemma countStudentsInWindowHelperLemma(times: seq<int>, start: int, T: int, i: int, j: int)
    requires T >= 1
    requires forall k :: 0 <= k < |times| ==> 1 <= times[k] <= 1000
    requires start >= 1
    requires 0 <= i <= j <= |times|
    ensures countStudentsInWindowHelper(times, start, T, i) >= countStudentsInWindowHelper(times, start, T, j)
    decreases j - i
{
    if i < j {
        var next := countStudentsInWindowHelper(times, start, T, i + 1);
        countStudentsInWindowHelperLemma(times, start, T, i + 1, j);
    }
}

lemma countStudentsInWindowHelperStep(times: seq<int>, start: int, T: int, i: int)
    requires T >= 1
    requires forall k :: 0 <= k < |times| ==> 1 <= times[k] <= 1000
    requires start >= 1
    requires 0 <= i < |times|
    ensures countStudentsInWindowHelper(times, start, T, i) == 
        (if start <= times[i] <= start + T - 1 then 1 else 0) + 
        countStudentsInWindowHelper(times, start, T, i + 1)
{
    // Explicit calculation to prove the step
    if i < |times| {
        // The function definition directly gives us this equality
    }
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
    var maxSeen := 0;
    var start := 1;
    while start <= 1000
        invariant 1 <= start <= 1001
        invariant maxSeen == maxStudentsInWindowUpTo(times, T, start - 1)
        decreases 1001 - start
    {
        var count := 0;
        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant count == countStudentsInWindowHelper(times, start, T, i)
            decreases n - i
        {
            // Apply the lemma to establish the relationship before modifying count
            countStudentsInWindowHelperStep(times, start, T, i);
            if start <= times[i] && times[i] <= start + T - 1 {
                count := count + 1;
            } else {
                // When the condition is false, count remains the same as the helper
                // which already excludes the current element
            }
            i := i + 1;
            // After incrementing i, we need to re-establish the invariant
            // The invariant holds because:
            // - When we increment i, we're moving to the next position
            // - The helper function is defined recursively and the lemma ensures correctness
        }
        
        assert count == countStudentsInWindow(times, start, T);
        
        var prev := maxSeen;
        if count > maxSeen {
            maxSeen := count;
        }
        maxStudentsInWindowUpToLemma(times, T, start);
        assert maxSeen == maxStudentsInWindowUpTo(times, T, start);
        start := start + 1;
    }
    result := maxSeen;
}
// </vc-code>

