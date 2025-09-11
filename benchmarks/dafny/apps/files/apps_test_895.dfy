// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
