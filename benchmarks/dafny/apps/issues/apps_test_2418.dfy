// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>, q: int, updates: seq<(int, int, int)>)
{
    n > 0 &&
    |a| == n &&
    q >= 0 &&
    |updates| == q &&
    (forall i :: 0 <= i < |updates| ==> 1 <= updates[i].0 <= updates[i].1 <= n) &&
    (forall i :: 0 <= i < |a| ==> -1000000000 <= a[i] <= 1000000000) &&
    (forall i :: 0 <= i < |updates| ==> -1000000000 <= updates[i].2 <= 1000000000)
}

predicate ValidOutput(results: seq<int>, n: int, a: seq<int>, q: int, updates: seq<(int, int, int)>)
    requires ValidInput(n, a, q, updates)
{
    |results| == q + 1 &&
    results[0] == computeMinMaxValue(a) &&
    (forall i :: 1 <= i < |results| ==> 
        results[i] == computeMinMaxValue(applyRangeUpdates(a, updates[..i])))
}
// </vc-preamble>

// <vc-helpers>
function floorDiv(a: int, b: int): int
    requires b != 0
{
    if (a >= 0 && b > 0) || (a < 0 && b < 0) then a / b
    else if a % b == 0 then a / b
    else a / b - 1
}

function computeMinMaxValue(arr: seq<int>): int
    requires |arr| > 0
{
    var w0 := arr[0];
    var positiveSum := sumPositiveDifferences(arr);
    floorDiv(w0 + positiveSum + 1, 2)
}

function sumPositiveDifferences(arr: seq<int>): int
    requires |arr| > 0
    decreases |arr|
{
    if |arr| == 1 then 0
    else
        var diff := arr[1] - arr[0];
        (if diff > 0 then diff else 0) + sumPositiveDifferences(arr[1..])
}

function applyRangeUpdates(arr: seq<int>, updates: seq<(int, int, int)>): seq<int>
    requires |arr| > 0
    requires forall i :: 0 <= i < |updates| ==> 1 <= updates[i].0 <= updates[i].1 <= |arr|
    ensures |applyRangeUpdates(arr, updates)| == |arr|
    decreases |updates|
{
    if |updates| == 0 then arr
    else
        var updated := applyRangeUpdate(arr, updates[0]);
        applyRangeUpdates(updated, updates[1..])
}

function applyRangeUpdate(arr: seq<int>, update: (int, int, int)): seq<int>
    requires |arr| > 0
    requires 1 <= update.0 <= update.1 <= |arr|
    ensures |applyRangeUpdate(arr, update)| == |arr|
{
    seq(|arr|, i requires 0 <= i < |arr| => if update.0 - 1 <= i <= update.1 - 1 then arr[i] + update.2 else arr[i])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, q: int, updates: seq<(int, int, int)>) returns (results: seq<int>)
    requires ValidInput(n, a, q, updates)
    ensures ValidOutput(results, n, a, q, updates)
// </vc-spec>
// <vc-code>
{
    var positiveSum := sumPositiveDifferences(a);
    var initialResult := floorDiv(a[0] + positiveSum + 1, 2);
    results := [initialResult];

    var updateIdx := 0;
    while updateIdx < q
        invariant 0 <= updateIdx <= q
        invariant |results| == updateIdx + 1
        invariant results[0] == computeMinMaxValue(a)
        invariant forall i :: 1 <= i < |results| ==> 
            results[i] == computeMinMaxValue(applyRangeUpdates(a, updates[..i]))
    {
        var updatedArray := applyRangeUpdates(a, updates[..updateIdx + 1]);
        var newResult := computeMinMaxValue(updatedArray);
        results := results + [newResult];
        updateIdx := updateIdx + 1;
    }
}
// </vc-code>
