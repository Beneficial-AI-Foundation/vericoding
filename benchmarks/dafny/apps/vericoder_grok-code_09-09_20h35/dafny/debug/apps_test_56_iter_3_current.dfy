predicate ValidInput(n: int, t: int) {
  1 <= n <= 10 && 0 <= t <= 10000
}

function TotalGlasses(n: int): int {
  n * (n + 1) / 2
}

predicate ValidResult(result: int, n: int, t: int) {
  result >= 0 && result <= TotalGlasses(n)
}

predicate CorrectForEdgeCases(result: int, n: int, t: int) {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}

// <vc-helpers>
// No changes needed in helpers for this fix.
// Existing definitions are sufficient.
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int) returns (result: int)
  requires ValidInput(n, t)
  ensures ValidResult(result, n, t)
  ensures CorrectForEdgeCases(result, n, t)
// </vc-spec>
// <vc-code>
{
  var glasses: seq<seq<real>> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |glasses| == i
    invariant forall j :: 0 <= j < i ==> |glasses[j]| == j + 1
  {
    var row: seq<real> := [];
    var j := 0;
    while j <= i
      invariant 0 <= j <= i + 1
      invariant |row| == j
    {
      row := row + [0.0];
      j := j + 1;
    }
    assert |row| == i + 1;
    glasses := glasses + [row];
    i := i + 1;
  }
  assert |glasses| == n;
  assert forall j :: 0 <= j < n ==> |glasses[j]| == j + 1;

  if t > 0 {
    var real_t: real := t as real;
    assert 0 <= 0 < |glasses| && 0 <= 0 < |glasses[0]|;
    glasses := glasses[0 := glasses[0][0 := real_t]];
  }

  i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |glasses| == n
    invariant forall j :: 0 <= j < n ==> |glasses[j]| == j + 1
  {
    var j := 0;
    while j <= i
      invariant 0 <= j <= i + 1
      invariant |glasses| == n
      invariant forall k :: 0 <= k < n ==> |glasses[k]| == k + 1
    {
      if glasses[i][j] > 1.0 {
        var excess: real := glasses[i][j] - 1.0;
        glasses := glasses[i := glasses[i][j := 1.0]];
        var next_excess: real := excess / 2.0;
        var next_row := glasses[i+1];
        assert 0 <= j < |next_row| && 0 <= j+1 < |next_row|;
        next_row := next_row[j := next_row[j] + next_excess];
        next_row := next_row[j+1 := next_row[j+1] + next_excess];
        glasses := glasses[i+1 := next_row];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var count: int := 0;
  var total_possible: int := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |glasses| == n
    invariant forall j :: 0 <= j < n ==> |glasses[j]| == j + 1
    invariant 0 <= count <= TotalGlasses(n)
    invariant 0 <= total_possible <= TotalGlasses(n)
    invariant total_possible == TotalGlasses(i)
  {
    var j := 0;
    while j <= i
      invariant 0 <= j <= i + 1
      invariant 0 <= count <= TotalGlasses(n)
      invariant 0 <= total_possible + (i+1 - j) <= TotalGlasses(n)
    {
      total_possible := total_possible + 1;
      if glasses[i][j] >= 1.0 {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := count;
}
// </vc-code>

