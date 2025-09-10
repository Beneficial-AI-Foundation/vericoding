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
  var results: seq<int> := [];
  for i := 0 to |testCases|-1 {
    var h := testCases[i].0;
    var m := testCases[i].1;
    var min := MinutesUntilMidnight(h, m);
    results := results + [min];
  }
}
// </vc-code>

