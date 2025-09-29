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
lemma MinutesUntilMidnightBounds(h: int, m: int)
    requires 0 <= h < 24
    requires 0 <= m < 60
    requires !(h == 0 && m == 0)
    ensures 1 <= MinutesUntilMidnight(h, m) <= 1439
{
    var totalMinutes := h * 60 + m;
    assert 1 <= totalMinutes <= 1439;
    assert MinutesUntilMidnight(h, m) == 1440 - totalMinutes;
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
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == MinutesUntilMidnight(testCases[j].0, testCases[j].1)
        invariant forall j :: 0 <= j < i ==> 1 <= results[j] <= 1439
    {
        var h := testCases[i].0;
        var m := testCases[i].1;
        var minutesLeft := 1440 - (h * 60 + m);
        
        MinutesUntilMidnightBounds(h, m);
        
        results := results + [minutesLeft];
        i := i + 1;
    }
}
// </vc-code>

