predicate ValidInput(holds: seq<int>) {
    |holds| >= 3 && forall i :: 0 <= i < |holds| - 1 ==> holds[i] < holds[i + 1]
}

function maxDiff(s: seq<int>): int
    requires |s| >= 2
    ensures maxDiff(s) >= 0
{
    if |s| <= 1 then 0
    else
        var maxSoFar := if s[1] - s[0] >= 0 then s[1] - s[0] else 0;
        maxDiffHelper(s, 2, maxSoFar)
}

function maxDiffHelper(s: seq<int>, index: int, currentMax: int): int
    requires 1 <= index <= |s|
    requires currentMax >= 0
    ensures maxDiffHelper(s, index, currentMax) >= currentMax
    decreases |s| - index
{
    if index >= |s| then currentMax
    else
        var diff := s[index] - s[index - 1];
        var newMax := if diff > currentMax then diff else currentMax;
        maxDiffHelper(s, index + 1, newMax)
}

// <vc-helpers>
lemma MaxDiffSeqProperties(s: seq<int>)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| - 1 ==> s[i + 1] - s[i] <= maxDiff(s)
    ensures exists i :: 0 <= i < |s| - 1 && s[i + 1] - s[i] == maxDiff(s)
{
}

lemma MaxDiffHelperLemma(s: seq<int>, index: int, currentMax: int)
    requires 1 <= index <= |s|
    requires currentMax >= 0
    ensures maxDiffHelper(s, index, currentMax) == 
        if index >= |s| then currentMax
        else maxDiffHelper(s, index + 1, 
            if s[index] - s[index - 1] > currentMax then s[index] - s[index - 1] else currentMax)
{
}

lemma MaxDiffConcatLemma(s: seq<int>, k: int, i: int)
    requires 1 <= k < |s| - 1
    requires 0 <= i < k - 1 || i >= k && i < |s| - 2
    requires ValidInput(s)
    ensures maxDiff(s[..k] + s[k+1..]) >= 
        if i < k - 1 then s[i + 1] - s[i]
        else s[i + 2] - s[i + 1]
{
}

lemma MaxDiffMinLemma(s: seq<int>, k: int, x: int)
    requires 1 <= k < |s| - 1
    requires ValidInput(s)
    requires x == maxDiff(s[..k] + s[k+1..])
    ensures forall i :: 1 <= i < |s| - 1 ==> x <= maxDiff(s[..i] + s[i+1..])
{
}
// </vc-helpers>

// <vc-spec>
method solve(holds: seq<int>) returns (result: int)
    requires ValidInput(holds)
    ensures result >= 0
    ensures exists k :: 1 <= k < |holds| - 1 && result == maxDiff(holds[..k] + holds[k+1..])
    ensures forall k :: 1 <= k < |holds| - 1 ==> result <= maxDiff(holds[..k] + holds[k+1..])
// </vc-spec>
// <vc-code>
{
    var best_result := maxDiff(holds[..1] + holds[2..]);
    var best_k := 1;
    
    var k := 2;
    while k < |holds| - 1
        invariant 1 <= k <= |holds| - 1
        invariant best_result >= 0
        invariant exists i :: 1 <= i < k && best_result == maxDiff(holds[..i] + holds[i+1..])
        invariant forall i :: 1 <= i < k ==> best_result <= maxDiff(holds[..i] + holds[i+1..])
    {
        var current_diff := maxDiff(holds[..k] + holds[k+1..]);
        if current_diff < best_result {
            best_result := current_diff;
            best_k := k;
        }
        k := k + 1;
    }
    
    result := best_result;
}
// </vc-code>

