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
function Max(a: int, b: int): int {
  if a >= b then a else b
}

lemma maxDiff_nonNegative(s: seq<int>)
  requires |s| >= 2
  ensures maxDiff(s) >= 0
{
}

lemma maxDiff_is_maximum(s: seq<int>, k: int, val: int)
    requires |s| >= 2
    requires 0 <= k < |s| - 1
    requires val == maxDiff(s[..k] + s[k+1..])
    ensures val >= 0
{}
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
    var N := |holds|;
    var maxOverallDiff := 0;
    var hasCalculatedOnce := false;

    for k := 1 to N - 2
        invariant 1 <= k <= N - 1
        invariant maxOverallDiff >= 0
        invariant forall i :: 1 <= i < k ==> maxOverallDiff >= maxDiff(holds[..i] + holds[i+1..])
        invariant (exists i :: 1 <= i < k && maxOverallDiff == maxDiff(holds[..i] + holds[i+1..]) && hasCalculatedOnce) || (k == 1 && !hasCalculatedOnce)
        invariant (k > 1 && hasCalculatedOnce) ==> (exists i :: 1 <= i < k && maxOverallDiff == maxDiff(holds[..i] + holds[i+1..]))
    {
        var currentSeq := holds[..k] + holds[k+1..];
        
        assert |currentSeq| == |holds| - 1;
        assert |currentSeq| >= 2;
        maxDiff_nonNegative(currentSeq); 

        if !hasCalculatedOnce {
            maxOverallDiff := maxDiff(currentSeq);
            hasCalculatedOnce := true;
        } else {
            maxOverallDiff := Max(maxOverallDiff, maxDiff(currentSeq));
        }
    }
    result := maxOverallDiff;
}
// </vc-code>

