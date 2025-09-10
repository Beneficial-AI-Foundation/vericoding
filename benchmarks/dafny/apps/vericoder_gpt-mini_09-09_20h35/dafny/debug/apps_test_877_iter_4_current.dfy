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
lemma ComputeFinalL_append(s: seq<(int,int)>, e: (int,int))
  ensures computeFinalL(s + [e]) == (if computeFinalL(s) > (if e.0 < e.1 then e.0 else e.1) then computeFinalL(s) else (if e.0 < e.1 then e.0 else e.1))
{
  var restL := computeFinalL(s);
  var minVal := if e.0 < e.1 then e.0 else e.1;
  assert computeFinalL(s + [e]) == (if restL > minVal then restL else minVal);
}

lemma ComputeFinalR_append(n: int, s: seq<(int,int)>, e: (int,int))
  ensures computeFinalR(n, s + [e]) == (if computeFinalR(n, s) < (if e.0 > e.1 then e.0 else e.1) then computeFinalR(n, s) else (if e.0 > e.1 then e.0 else e.1))
{
  var restR := computeFinalR(n, s);
  var maxVal := if e.0 > e.1 then e.0 else e.1;
  assert computeFinalR(n, s + [e]) == (if restR < maxVal then restR else maxVal);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var l := 1;
  var r := n;
  while i < |pairs|
    invariant 0 <= i <= |pairs|
    invariant l == computeFinalL(pairs[..i])
    invariant r == computeFinalR(n, pairs[..i])
    invariant 1 <= l <= n
    invariant 1 <= r <= n
    decreases |pairs| - i
  {
    var oldl := l;
    var oldr := r;
    var s := pairs[..i];
    var e := pairs[i];
    var minVal := if e.0 < e.1 then e.0 else e.1;
    var maxVal := if e.0 > e.1 then e.0 else e.1;

    // connect old values with computeFinal functions on the prefix s
    assert oldl == computeFinalL(s);
    assert oldr == computeFinalR(n, s);

    ComputeFinalL_append(s, e);
    ComputeFinalR_append(n, s, e);

    l := if oldl > minVal then oldl else minVal;
    r := if oldr < maxVal then oldr else maxVal;
    i := i + 1;

    assert l == computeFinalL(pairs[..i]);
    assert r == computeFinalR(n, pairs[..i]);
    assert 1 <= l <= n;
    assert 1 <= r <= n;
  }
  assert l == computeFinalL(pairs);
  assert r == computeFinalR(n, pairs);

  var diff := r - l;
  if diff < 0 {
    result := 0;
  } else {
    result := diff;
  }

  // prove postconditions
  assert result == (if r - l > 0 then r - l else 0);
  assert result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0);
  assert 0 <= result;
  assert r <= n;
  assert l >= 1;
  assert r - l <= n - 1;
  assert result <= n - 1;
}
// </vc-code>

