predicate ValidInput(test_cases: seq<(int, int)>)
{
    forall i :: 0 <= i < |test_cases| ==> 
        test_cases[i].0 > 0 && test_cases[i].1 > 0
}

function MinMovesToDivisible(a: int, b: int): int
    requires a > 0 && b > 0
{
    (b - a % b) % b
}

predicate ValidOutput(test_cases: seq<(int, int)>, results: seq<int>)
    requires ValidInput(test_cases)
{
    |results| == |test_cases| &&
    forall i :: 0 <= i < |results| ==> 
        results[i] == MinMovesToDivisible(test_cases[i].0, test_cases[i].1) &&
        results[i] >= 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures ValidOutput(test_cases, results)
// </vc-spec>
// <vc-code>
{
  var n := |test_cases|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == MinMovesToDivisible(test_cases[j].0, test_cases[j].1) && arr[j] >= 0
    decreases n - i
  {
    assert 0 <= i < |test_cases|;
    assert test_cases[i].0 > 0 && test_cases[i].1 > 0;
    var a := test_cases[i].0;
    var b := test_cases[i].1;
    var r := MinMovesToDivisible(a, b);
    assert r >= 0;
    arr[i] := r;
    i := i + 1;
  }
  results := arr[..];
}
// </vc-code>

