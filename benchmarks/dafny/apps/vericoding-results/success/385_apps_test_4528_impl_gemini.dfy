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
lemma MinutesUntilMidnightIsValid(h: int, m: int)
  requires 0 <= h < 24
  requires 0 <= m < 60
  requires !(h == 0 && m == 0)
  ensures 1 <= MinutesUntilMidnight(h, m) <= 1439
{
  var total_minutes := h * 60 + m;
  if h > 0 {
    assert total_minutes >= 60;
  } else { // h == 0
    assert m > 0;
    assert total_minutes >= 1;
  }
  assert total_minutes >= 1;

  assert h <= 23 && m <= 59;
  calc {
    total_minutes;
    == h * 60 + m;
    <= 23 * 60 + m;
    <= 23 * 60 + 59;
    == 1439;
  }
  assert total_minutes <= 1439;
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
    invariant forall k :: 0 <= k < i ==> results[k] == MinutesUntilMidnight(testCases[k].0, testCases[k].1)
    invariant ValidOutput(results)
  {
    var h := testCases[i].0;
    var m := testCases[i].1;
    var res := MinutesUntilMidnight(h, m);
    MinutesUntilMidnightIsValid(h, m);
    results := results + [res];
    i := i + 1;
  }
}
// </vc-code>

