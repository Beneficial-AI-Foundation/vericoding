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
function ComputeIncreasingEnd(arr: seq<int>, start: int, currentEnd: int): int
    requires 0 <= start <= currentEnd <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures ComputeIncreasingEnd(arr, start, currentEnd) >= currentEnd
    ensures ComputeIncreasingEnd(arr, start, currentEnd) <= |arr|
    decreases |arr| - currentEnd
{
    if currentEnd >= |arr| then currentEnd
    else if currentEnd == 0 then ComputeIncreasingEnd(arr, start, 1)
    else if arr[currentEnd-1] < arr[currentEnd] then ComputeIncreasingEnd(arr, start, currentEnd + 1)
    else currentEnd
}

function ComputeConstantEnd(arr: seq<int>, start: int, value: int): int
    requires 0 <= start <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires value >= 0
    ensures ComputeConstantEnd(arr, start, value) >= start
    ensures ComputeConstantEnd(arr, start, value) <= |arr|
    decreases |arr| - start
{
    if start >= |arr| then start
    else if value == 0 then start
    else if arr[start] == value then ComputeConstantEnd(arr, start + 1, value)
    else start
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, value: int): int
    requires 0 <= start <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires value >= 0
    ensures ComputeDecreasingEnd(arr, start, value) >= start
    ensures ComputeDecreasingEnd(arr, start, value) <= |arr|
    decreases |arr| - start
{
    if start >= |arr| then |arr|
    else if value == 0 then |arr|
    else if start == 0 then |arr|
    else if arr[start] < value then 
        ComputeDecreasingEnd(arr, start + 1, arr[start])
    else start
}

lemma ComputePhasesProperties(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr);
        0 <= incEnd <= constEnd <= decEnd <= |arr|
{
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constValue := if incEnd > 0 && incEnd <= |arr| then arr[incEnd-1] else 0;
    var constEnd := ComputeConstantEnd(arr, incEnd, constValue);
    var decValue := if constEnd > incEnd && incEnd < |arr| then arr[incEnd] else constValue;
    var decEnd := ComputeDecreasingEnd(arr, constEnd, decValue);
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
    if |arr| <= 1 {
        result := "YES";
    } else {
        var phases := ComputePhases(arr);
        var incEnd := phases.0;
        var constEnd := phases.1;
        var decEnd := phases.2;
        
        if !(incEnd <= constEnd && constEnd <= decEnd && decEnd == |arr|) {
            result := "NO";
            return;
        }
        
        // Check increasing phase
        if incEnd > 1 {
            var i := 0;
            while i < incEnd - 1
                invariant 0 <= i <= incEnd - 1
                invariant forall j, k :: 0 <= j < k < i + 1 ==> arr[j] < arr[k]
            {
                if arr[i] >= arr[i + 1] {
                    result := "NO";
                    return;
                }
                i := i + 1;
            }
        }
        
        // Check constant phase
        if incEnd < constEnd {
            var constValue := if incEnd > 0 then arr[incEnd] else arr[0];
            var i := incEnd;
            while i < constEnd
                invariant incEnd <= i <= constEnd
                invariant forall j :: incEnd <= j < i ==> arr[j] == constValue
            {
                if arr[i] != constValue {
                    result := "NO";
                    return;
                }
                i := i + 1;
            }
        }
        
        // Check decreasing phase
        if constEnd < decEnd && decEnd > 1 {
            var i := constEnd;
            while i < decEnd - 1
                invariant constEnd <= i <= decEnd - 1
                invariant forall j, k :: constEnd <= j < k < i + 1 ==> arr[j] > arr[k]
            {
                if arr[i] <= arr[i + 1] {
                    result := "NO";
                    return;
                }
                i := i + 1;
            }
        }
        
        // Check transition condition
        if incEnd > 0 && constEnd < |arr| {
            var leftValue := arr[incEnd - 1];
            var rightValue := if constEnd > incEnd then arr[incEnd] else arr[constEnd];
            if leftValue < rightValue {
                result := "NO";
                return;
            }
        }
        
        result := "YES";
    }
}
// </vc-code>

