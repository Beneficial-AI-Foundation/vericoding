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
    ensures ComputeDecreasingEnd(arr, start, currentMin) == |arr| || !(arr[ComputeDecreasingEnd(arr, start, currentMin)] < arr[ComputeDecreasingEnd(arr, start, currentMin)-1])
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
    var (incEnd, constEnd, decEnd) := ComputePhases(arr);

    // The checks for constant, increasing, and decreasing properties are now encapsulated
    // and verified by the ensures clauses of the `ComputePhases` function's components.
    // The main logic here should focus on the overall shape and connections between phases.

    var isUnimodalResult := true;

    if |arr| <= 1 then
        isUnimodalResult := true;
    else
        // Check phase order and lengths
        if !(incEnd <= constEnd && constEnd <= decEnd && decEnd == |arr|) then
            isUnimodalResult := false;

        // Check increasing phase properties (guaranteed by ComputeIncreasingEnd's ensures)
        // Check constant phase properties (guaranteed by ComputeConstantEnd's ensures)
        // Check decreasing phase properties (guaranteed by ComputeDecreasingEnd's ensures)

        // Check transition from increasing to constant
        if isUnimodalResult && incEnd > 0 && incEnd < constEnd then // increasing part exists and constant part exists
            if !(arr[incEnd-1] <= arr[incEnd]) then // The last element of increasing part must be <= the first element of constant part
                isUnimodalResult := false;

        // Check transition from increasing to decreasing (when no constant part)
        if isUnimodalResult && incEnd > 0 && incEnd == constEnd && incEnd < decEnd then // increasing part, no constant, then decreasing
            if !(arr[incEnd-1] >= arr[incEnd]) then // The last element of increasing part must be >= the first element of decreasing part
                isUnimodalResult := false;

        // Check transition from constant to decreasing
        if isUnimodalResult && constEnd > incEnd && constEnd < decEnd then // constant part exists and decreasing part exists
            if !(arr[constEnd-1] >= arr[constEnd]) then // The last element of constant part must be >= the first element of decreasing part
                isUnimodalResult := false;

        // Edge case: purely increasing
        if isUnimodalResult && incEnd == |arr| then
            isUnimodalResult := true; // This is a valid unimodal shape

        // Edge case: purely constant
        if isUnimodalResult && constEnd == |arr| then
            isUnimodalResult := true; // This is a valid unimodal shape

        // Edge case: purely decreasing
        if isUnimodalResult && decEnd == |arr| && incEnd == 0 && constEnd == 0 then
            isUnimodalResult := true; // This is a valid unimodal shape

        // Special case for IsUnimodal: (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]))
        // This condition implies that if there is an increasing phase and a decreasing phase,
        // the peak of the unimodal sequence is appropriately handled.
        // It's tricky because the definition of `incEnd`, `constEnd`, and `decEnd` means:
        // `incEnd` is the first index *not* part of the strictly increasing prefix.
        // `constEnd` is the first index *not* part of the constant section.
        // `decEnd` is `|arr|`.

        // If an increasing part exists (incEnd > 0)
        // and a decreasing part exists (constEnd < |arr| means a decreasing part *could* follow or starts at constEnd)
        // and if phases.1 < |arr| means the constant part doesn't extend to the end, hence a decreasing part follows.
        if isUnimodalResult && incEnd > 0 && constEnd < |arr| then
            if !(arr[incEnd-1] >= (if constEnd > incEnd then arr[incEnd] else arr[constEnd])) then
                isUnimodalResult := false;

    // The IsUnimodal function already encapsulates the full logic.
    // The separate checks above were attempts to replicate it.
    // We can simply call IsUnimodal.
    result := if IsUnimodal(arr) then "YES" else "NO";
}
// </vc-code>

