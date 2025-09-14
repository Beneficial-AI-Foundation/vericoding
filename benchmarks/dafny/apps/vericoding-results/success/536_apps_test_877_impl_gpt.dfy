predicate ValidInput(n: int, m: int, pairs: seq<(int, int)>)
{
    n >= 2 && 
    m >= 0 && 
    |pairs| == m &&
    (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n) &&
    (forall i :: 0 <= i < |pairs| ==> pairs[i].0 != pairs[i].1)
}

function computeFinalL(pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then 1
    else 
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeFinalL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

function computeFinalR(n: int, pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeFinalR(n, pairs[..|pairs|-1]);
        if restR < maxVal then restR else maxVal
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

predicate ValidResult(n: int, pairs: seq<(int, int)>, result: int)
{
    result >= 0 &&
    result <= n - 1 &&
    result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0)
}

// <vc-helpers>
lemma ComputeFinalL_bounds(n: int, pairs: seq<(int,int)>)
  requires n >= 1
  requires forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n
  ensures 1 <= computeFinalL(pairs) <= n
  decreases |pairs|
{
  if |pairs| == 0 {
    assert computeFinalL(pairs) == 1;
  } else {
    assert forall i {:trigger pairs[..|pairs|-1][i]} :: 0 <= i < |pairs[..|pairs|-1]| ==>
      1 <= pairs[..|pairs|-1][i].0 <= n && 1 <= pairs[..|pairs|-1][i].1 <= n;
    var rest := computeFinalL(pairs[..|pairs|-1]);
    ComputeFinalL_bounds(n, pairs[..|pairs|-1]);
    assert 1 <= rest <= n;

    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    assert 1 <= x <= n;
    assert 1 <= y <= n;

    var minVal := if x < y then x else y;
    assert 1 <= minVal <= n;

    assert computeFinalL(pairs) == (if rest > minVal then rest else minVal);

    if rest > minVal {
      assert computeFinalL(pairs) == rest;
      assert 1 <= computeFinalL(pairs) <= n;
    } else {
      assert computeFinalL(pairs) == minVal;
      assert 1 <= computeFinalL(pairs) <= n;
    }
  }
}

lemma ComputeFinalR_bounds(n: int, pairs: seq<(int,int)>)
  requires n >= 1
  requires forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n
  ensures 1 <= computeFinalR(n, pairs) <= n
  decreases |pairs|
{
  if |pairs| == 0 {
    assert computeFinalR(n, pairs) == n;
    assert 1 <= computeFinalR(n, pairs) <= n;
  } else {
    assert forall i {:trigger pairs[..|pairs|-1][i]} :: 0 <= i < |pairs[..|pairs|-1]| ==>
      1 <= pairs[..|pairs|-1][i].0 <= n && 1 <= pairs[..|pairs|-1][i].1 <= n;
    var rest := computeFinalR(n, pairs[..|pairs|-1]);
    ComputeFinalR_bounds(n, pairs[..|pairs|-1]);
    assert 1 <= rest <= n;

    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    assert 1 <= x <= n;
    assert 1 <= y <= n;

    var maxVal := if x > y then x else y;
    assert 1 <= maxVal <= n;

    assert computeFinalR(n, pairs) == (if rest < maxVal then rest else maxVal);

    if rest < maxVal {
      assert computeFinalR(n, pairs) == rest;
      assert 1 <= computeFinalR(n, pairs) <= n;
    } else {
      assert computeFinalR(n, pairs) == maxVal;
      assert 1 <= computeFinalR(n, pairs) <= n;
    }
  }
}

lemma MaxDiffBound(n: int, L: int, R: int)
  requires n >= 2
  requires 1 <= L <= n
  requires 1 <= R <= n
  ensures max(R - L, 0) <= n - 1
{
  assert R - L <= n - L;
  assert n - L <= n - 1;
  assert R - L <= n - 1;
  assert 0 <= n - 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
  var L := computeFinalL(pairs);
  var R := computeFinalR(n, pairs);

  ComputeFinalL_bounds(n, pairs);
  ComputeFinalR_bounds(n, pairs);

  var diff := R - L;
  if diff > 0 {
    result := diff;
  } else {
    result := 0;
  }

  MaxDiffBound(n, L, R);

  if diff > 0 {
    assert max(diff, 0) == diff;
  } else {
    assert max(diff, 0) == 0;
  }
}
// </vc-code>

