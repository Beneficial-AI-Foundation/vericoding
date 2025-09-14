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
  var res: seq<int> := [];
  var i := 0;
  while i < |testCases|
    invariant 0 <= i <= |testCases|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == MinutesUntilMidnight(testCases[j].0, testCases[j].1)
    invariant forall j :: 0 <= j < i ==> 1 <= res[j] <= 1439
  {
    var h := testCases[i].0;
    var m := testCases[i].1;

    // From ValidInput and loop bounds
    assert 0 <= i < |testCases|;
    assert 0 <= h < 24 && 0 <= m < 60 && !(h == 0 && m == 0);

    var v := MinutesUntilMidnight(h, m);

    // Prove bounds for v
    assert 0 <= h*60 + m <= 1439;
    // Show h*60 + m >= 1 using !(h==0 && m==0)
    if h == 0 {
      assert m > 0;
      assert h*60 + m >= 1;
    } else {
      assert h >= 1;
      assert h*60 >= 60;
      assert h*60 + m >= 60;
    }
    assert 1 <= 1440 - (h*60 + m) <= 1439;

    res := res + [v];
    i := i + 1;
  }
  results := res;
}
// </vc-code>

