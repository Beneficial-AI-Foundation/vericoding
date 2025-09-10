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
// </vc-helpers>
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
    var n := |holds| - 1;
    var diffs := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall x :: 0 <= x < i ==> diffs[x] == holds[x+1] - holds[x]
    {
        diffs[i] := holds[i+1] - holds[i];
        i := i + 1;
    }
    var max1 := 0;
    var second := 0;
    var max1_pos := -1;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant 0 <= second <= max1
        invariant max1_pos < j <= n
        invariant forall x :: 0 <= x < j ==> diffs[x] <= max1 
        invariant forall x :: 0 <= x < j ==> (diffs[x] < max1) || diffs[x] == max1 
        invariant (max1_pos != -1 ==> diffs[max1_pos] == max1)
    {
        var d := diffs[j];
        if d > max1 {
            second := max1;
            max1 := d;
            max1_pos := j;
        } else if d > second {
            second := d;
        }
        j := j + 1;
    }
    var resultVal := max1;
    var k := 1;
    while k < n - 1
        invariant 1 <= k <= n - 1
        invariant resultVal >= 0
    {
        var new_diff := diffs[k-1] + diffs[k];
        var current_max_for_this := if new_diff > 0 then new_diff else 0;
        var p := 0;
        while p < n
            invariant 0 <= p <= n
            invariant 0 <= current_max_for_this
        {
            if p != k - 1 && p != k {
                if diffs[p] > current_max_for_this {
                    current_max_for_this := diffs[p];
                }
            }
            p := p + 1;
        }
        if current_max_for_this < resultVal || current_max_for_this == resultVal {
            resultVal := current_max_for_this;
        }
        k := k + 1;
    }
    result := resultVal;
}
// </vc-code>

