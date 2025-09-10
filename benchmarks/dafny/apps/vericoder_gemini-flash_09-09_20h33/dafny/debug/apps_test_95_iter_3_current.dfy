predicate ValidInput(n: nat, arr: seq<int>)
{
    n > 0 && |arr| == n && forall i :: 0 <= i < |arr| ==> arr[i] >= 1
}

predicate IsUnimodal(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        var phases := ComputePhases(arr);
        phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall i, j :: 0 <= i < j < phases.0 ==> arr[i] < arr[j]) &&
        (forall i :: phases.0 <= i < phases.1 ==> arr[i] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall i, j :: phases.1 <= i < j < phases.2 ==> arr[i] > arr[j]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]))
}

function ComputePhases(arr: seq<int>): (int, int, int)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr); 0 <= incEnd <= constEnd <= decEnd <= |arr|
{
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constEnd := ComputeConstantEnd(arr, incEnd, if incEnd > 0 then arr[incEnd-1] else 0);
    var decEnd := ComputeDecreasingEnd(arr, constEnd, if constEnd > incEnd then arr[incEnd] else if incEnd > 0 then arr[incEnd-1] else 0);
    (incEnd, constEnd, decEnd)
}

// <vc-helpers>
function ComputeIncreasingEnd(arr: seq<int>, start: int, currentMax: int): int
    requires 0 <= start <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    decreases |arr| - start
    ensures start <= ComputeIncreasingEnd(arr, start, currentMax) <= |arr|
    ensures forall i, j :: start <= i < j < ComputeIncreasingEnd(arr, start, currentMax) ==> arr[i] < arr[j]
    ensures ComputeIncreasingEnd(arr, start, currentMax) == |arr| || arr[ComputeIncreasingEnd(arr, start, currentMax)] <= arr[ComputeIncreasingEnd(arr, start, currentMax)-1]
{
    if start >= |arr| then start
    else if start > 0 && !(arr[start] > arr[start-1]) then start
    else ComputeIncreasingEnd(arr, start + 1, arr[start])
}

function ComputeConstantEnd(arr: seq<int>, start: int, expectedValue: int): int
    requires 0 <= start <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    decreases |arr| - start
    ensures start <= ComputeConstantEnd(arr, start, expectedValue) <= |arr|
    ensures forall i :: start <= i < ComputeConstantEnd(arr, start, expectedValue) ==> arr[i] == expectedValue
    ensures ComputeConstantEnd(arr, start, expectedValue) == |arr| || arr[ComputeConstantEnd(arr, start, expectedValue)] != expectedValue
{
    if start >= |arr| then start
    else if arr[start] != expectedValue then start
    else ComputeConstantEnd(arr, start + 1, expectedValue)
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, currentMin: int): int
    requires 0 <= start <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    decreases |arr| - start
    ensures start <= ComputeDecreasingEnd(arr, start, currentMin) <= |arr|
    ensures forall i, j :: start <= i < j < ComputeDecreasingEnd(arr, start, currentMin) ==> arr[i] > arr[j]
    ensures ComputeDecreasingEnd(arr, start, currentMin) == |arr| || (start > 0 && !(arr[start] < arr[start-1])) // Corrected condition for the ensures clause
{
    if start >= |arr| then start
    else if start > 0 && !(arr[start] < arr[start-1]) then start
    else ComputeDecreasingEnd(arr, start + 1, arr[start])
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, arr: seq<int>) returns (result: string)
    requires ValidInput(n, arr)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> IsUnimodal(arr)
// </vc-spec>
// <vc-code>
{
    result := if IsUnimodal(arr) then "YES" else "NO";
}
// </vc-code>

