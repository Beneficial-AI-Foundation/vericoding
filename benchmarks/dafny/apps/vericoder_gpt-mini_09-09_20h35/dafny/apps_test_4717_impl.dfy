predicate ValidInput(x: int, a: int, b: int)
{
    1 <= x <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    x != a && x != b && a != b &&
    Distance(x, a) != Distance(x, b)
}

function Distance(s: int, t: int): nat
{
    if s >= t then s - t else t - s
}

predicate CorrectResult(x: int, a: int, b: int, result: string)
{
    (result == "A" <==> Distance(x, a) < Distance(x, b)) &&
    (result == "B" <==> Distance(x, b) < Distance(x, a))
}

// <vc-helpers>
lemma NotLtImplEq(a:int, b:int)
  ensures (! (a < b) && ! (b < a)) ==> a == b
{
  if ! (a < b) && ! (b < a) {
    assert a >= b;
    assert b >= a;
    assert a == b;
  }
}

lemma DistinctCompare(a:int, b:int)
  requires a != b
  ensures a < b || b < a
{
  if a < b {
  } else if b < a {
  } else {
    NotLtImplEq(a, b);
    assert a == b;
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, a: int, b: int) returns (result: string)
requires ValidInput(x, a, b)
ensures result == "A" || result == "B"
ensures CorrectResult(x, a, b, result)
// </vc-spec>
// <vc-code>
{
  var da := Distance(x, a);
  var db := Distance(x, b);
  if da < db {
    result := "A";
  } else {
    DistinctCompare(da, db);
    assert db < da;
    result := "B";
  }
}
// </vc-code>

