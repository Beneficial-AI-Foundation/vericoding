predicate ValidInput(testCases: seq<(int, int)>)
{
    forall i :: 0 <= i < |testCases| ==> 
        0 <= testCases[i].0 < 24 && 
        0 <= testCases[i].1 < 60 && 
        !(testCases[i].0 == 0 && testCases[i].1 == 0)
}

function MinutesUntilMidnight(h: int, m: int): int
    requires 0 <= h < 24
    requires 0 <= m < 60
    requires !(h == 0 && m == 0)
{
    1440 - (h * 60 + m)
}

predicate ValidOutput(results: seq<int>)
{
    forall i :: 0 <= i < |results| ==> 1 <= results[i] <= 1439
}

// <vc-helpers>
lemma MinutesUntilMidnightProperties(h: int, m: int)
    requires 0 <= h < 24
    requires 0 <= m < 60
    requires !(h == 0 && m == 0)
    ensures 1 <= MinutesUntilMidnight(h, m) <= 1439
{
    // Total minutes in a day from (h, m) to midnight
    var total_minutes := h * 60 + m;
    
    // Minimum case: (0, 1) gives 1439 minutes
    // Maximum case: (23, 59) gives 1 minute
    assert total_minutes >= 1 && total_minutes <= 23 * 60 + 59;
    assert total_minutes >= 1 && total_minutes <= 1439;
    
    var result := 1440 - total_minutes;
    assert result >= 1440 - 1439 && result <= 1440 - 1;
    assert result >= 1 && result <= 1439;
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures |results| == |testCases|
    ensures forall i :: 0 <= i < |results| ==> results[i] == MinutesUntilMidnight(testCases[i].0, testCases[i].1)
    ensures ValidOutput(results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |testCases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == MinutesUntilMidnight(testCases[j].0, testCases[j].1)
        invariant ValidOutput(results)
    {
        var h := testCases[i].0;
        var m := testCases[i].1;
        MinutesUntilMidnightProperties(h, m);
        results := results + [MinutesUntilMidnight(h, m)];
        i := i + 1;
    }
}
// </vc-code>

