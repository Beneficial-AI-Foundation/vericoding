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
// (no helpers needed)
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
  var res := ([] : seq<int>);
  var i := 0;
  while i < |testCases|
    invariant 0 <= i <= |testCases|;
    invariant |res| == i;
    invariant forall j :: 0 <= j < |res| ==>
        0 <= testCases[j].0 < 24 && 0 <= testCases[j].1 < 60 && !(testCases[j].0 == 0 && testCases[j].1 == 0);
    invariant forall j :: 0 <= j < |res| ==> res[j] == MinutesUntilMidnight(testCases[j].0, testCases[j].1)
  {
    var h := testCases[i].0;
    var m := testCases[i].1;
    assert 0 <= h < 24 && 0 <= m < 60 && !(h == 0 && m == 0);
    res := res + [MinutesUntilMidnight(h, m)];
    i := i + 1;
  }
  results := res;
}
// </vc-code>

