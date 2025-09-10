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
function ComputeIncreasingEnd(arr: seq<int>, i: int, dummy: int): int
    requires 0 <= i <= |arr|
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    decreases |arr| - i
    ensures 0 <= ComputeIncreasingEnd(arr, i, dummy) <= |arr|
    ensures ComputeIncreasingEnd(arr, i, dummy) >= i
{
    if i + 1 >= |arr| then |arr|
    else if arr[i] < arr[i+1] then ComputeIncreasingEnd(arr, i+1, dummy)
    else i + 1
}

function ComputeConstantEnd(arr: seq<int>, start: int, value: int): int
    requires 0 <= start <= |arr|
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    decreases |arr| - start
    ensures start <= ComputeConstantEnd(arr, start, value) <= |arr|
{
    if start >= |arr| then |arr|
    else if arr[start] == value then ComputeConstantEnd(arr, start+1, value)
    else start
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, prev: int): int
    requires 0 <= start <= |arr|
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    decreases |arr| - start
    ensures start <= ComputeDecreasingEnd(arr, start, prev) <= |arr|
{
    if start >= |arr| then |arr|
    else if prev > arr[start] then ComputeDecreasingEnd(arr, start+1, arr[start])
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
  if IsUnimodal(arr) {
    return "YES";
  } else {
    return "NO";
  }
}
// </vc-code>

