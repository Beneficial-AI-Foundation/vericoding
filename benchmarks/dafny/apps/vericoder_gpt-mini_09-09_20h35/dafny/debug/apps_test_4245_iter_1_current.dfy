predicate ValidInput(a: int, b: int)
{
  a > 1 && b >= 0
}

function SocketsAfterStrips(strips: int, a: int): int
  requires a > 1 && strips >= 0
{
  1 + strips * (a - 1)
}

function CeilingDivision(x: int, y: int): int
  requires y > 0
{
  if x % y == 0 then x / y
  else if x >= 0 then x / y + 1
  else x / y
}

function MinStripsNeeded(a: int, b: int): int
  requires ValidInput(a, b)
{
  if b <= 1 then 0
  else CeilingDivision(b - 1, a - 1)
}

predicate CorrectResult(a: int, b: int, result: int)
  requires ValidInput(a, b)
{
  result >= 0 &&
  SocketsAfterStrips(result, a) >= b &&
  (result == 0 || SocketsAfterStrips(result - 1, a) < b)
}

// <vc-helpers>
lemma CeilingDivision_props(x: int, y: int)
  requires y > 0 && x >= 0
  ensures CeilingDivision(x, y) >= 0
  ensures CeilingDivision(x, y) * y >= x
  ensures (CeilingDivision(x, y) == 0) || ((CeilingDivision(x, y) - 1) * y < x)
{
  var k := CeilingDivision(x, y);
  if x % y == 0 {
    assert k == x / y;
    // x == y*(x/y) + x%y and x%y == 0 implies x == y*(x/y)
    assert x == y * (x / y);
    assert k * y == x;
    assert k >= 0;
    if k != 0 {
      assert (k - 1) * y == k * y - y;
      assert k * y - y < k * y;
      assert (k - 1) * y < x;
    }
  } else {
    assert k == x / y + 1;
    // x == y*(x/y) + x%y and 0 < x%y < y implies (x/y)*y = x - x%y < x
    assert (k - 1) * y == (x / y) * y;
    assert (x / y) * y == x - x % y;
    assert 0 < x % y < y;
    assert (k - 1) * y < x;
    assert k >= 0;
    assert k * y == (x / y + 1) * y;
    assert k * y == (x / y) * y + y;
    assert k * y >= x;
  }
}

lemma MinStripsNeeded_Correct(a: int, b: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, MinStripsNeeded(a, b))
{
  if b <= 1 {
    // MinStripsNeeded == 0
    assert MinStripsNeeded(a, b) == 0;
    // non-negativity
    assert MinStripsNeeded(a, b) >= 0;
    // sockets after 0 strips is 1, which is >= b since b <= 1
    assert SocketsAfterStrips(0, a) == 1;
    assert 1 >= b;
    // minimality: result == 0 satisfies (result == 0) or ...
  } else {
    var k := MinStripsNeeded(a, b);
    assert k == CeilingDivision(b - 1, a - 1);
    // apply ceiling properties for x = b-1, y = a-1
    call CeilingDivision_props(b - 1, a - 1);
    assert k >= 0;
    // k*(a-1) >= b-1  => 1 + k*(a-1) >= b
    assert k * (a - 1) >= b - 1;
    assert SocketsAfterStrips(k, a) == 1 + k * (a - 1);
    assert SocketsAfterStrips(k, a) >= b;
    // minimality: (k == 0) || (k-1)*(a-1) < b-1
    if k == 0 {
      // then CorrectResult allows result == 0
    } else {
      assert (k - 1) * (a - 1) < b - 1;
      assert SocketsAfterStrips(k - 1, a) == 1 + (k - 1) * (a - 1);
      assert SocketsAfterStrips(k - 1, a) < b;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, result)
// </vc-spec>
// <vc-code>
{
  result := MinStripsNeeded(a, b);
  call MinStripsNeeded_Correct(a, b);
}
// </vc-code>

