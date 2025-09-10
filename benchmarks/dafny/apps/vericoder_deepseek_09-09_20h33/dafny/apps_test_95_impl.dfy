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
function ComputeIncreasingEnd(arr: seq<int>, start: int, last: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires last >= 0
    ensures start <= ComputeIncreasingEnd(arr, start, last) <= |arr|
    ensures forall i, j :: start <= i < j < ComputeIncreasingEnd(arr, start, last) ==> arr[i] < arr[j]
    decreases |arr| - start
{
    if start >= |arr| then |arr|
    else if arr[start] > last then ComputeIncreasingEnd(arr, start + 1, arr[start])
    else start
}

function ComputeConstantEnd(arr: seq<int>, start: int, last: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires last >= 0
    ensures start <= ComputeConstantEnd(arr, start, last) <= |arr|
    ensures forall i :: start <= i < ComputeConstantEnd(arr, start, last) ==> arr[i] == last
    decreases |arr| - start
{
    if start >= |arr| then |arr|
    else if arr[start] == last then ComputeConstantEnd(arr, start + 1, last)
    else start
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, last: int): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    requires last >= 0
    ensures start <= ComputeDecreasingEnd(arr, start, last) <= |arr|
    ensures forall i, j :: start <= i < j < ComputeDecreasingEnd(arr, start, last) ==> arr[i] > arr[j]
    decreases |arr| - start
{
    if start >= |arr| then |arr|
    else if arr[start] < last then ComputeDecreasingEnd(arr, start + 1, arr[start])
    else start
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
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constEnd := ComputeConstantEnd(arr, incEnd, if incEnd > 0 then arr[incEnd-1] else 0);
    var decEnd := ComputeDecreasingEnd(arr, constEnd, if constEnd > incEnd then arr[incEnd] else if incEnd > 0 then arr[incEnd-1] else 0);
    
    if incEnd <= constEnd && constEnd <= decEnd && decEnd == |arr| &&
        (forall i, j :: 0 <= i < j < incEnd ==> arr[i] < arr[j]) &&
        (forall i :: incEnd <= i < constEnd ==> arr[i] == (if incEnd > 0 then arr[incEnd] else arr[0])) &&
        (forall i, j :: constEnd <= i < j < decEnd ==> arr[i] > arr[j]) &&
        (incEnd > 0 && constEnd < |arr| ==> arr[incEnd-1] >= (if constEnd > incEnd then arr[incEnd] else arr[constEnd]))
    {
        result := "YES";
    }
    else
    {
        result := "NO";
    }
}
// </vc-code>

