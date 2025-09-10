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
  else Ce markdownilingDivision(b - 1, a - 1)
}

predicate CorrectResult(a: int, b: int, result: int)
  requires ValidInput(a, b)
{
  result >= 0 &&
  SocketsAfterStrips(result, a) >= b &&
  (result == 0 || SocketsAfterStrips(result - 1, a) < b)
}

lemma SocketsAfterStripsNonDecreasing()
{
  forall a: int, strips: int | a > 1 && strips >= 0 {
    assert SocketsAfterStrips(strips, a) == 1 + strips * (a - 1);
  }
}

lemma SocketsAfterStripsCorrect(strips: int, a: int, b: int)
  requires a > 1 && b >= 0 && strips >= 0
{
  assert SocketsAfterStrips(strips, a) == 1 + strips * (a - 1);
}

lemma CeilingDivisionIsCeil(x: int, y: int)
  requires y > 0
{
  var d := CeilingDivision(x, y);
  var r := x % y;
  var q := x / y;
  if r == 0 {
    assert d == q;
    assert d * y == x;
    assert true;
  } else if x >= 0 {
    assert d == q + 1;
    assert q * y <= x;
    assert q * y + r == x;
    assert r < y;
    assert d * y == q * y + r + y - r;
  } else {
    assert d == q;
  }
}

lemma CeilingDivisionAtLeast(x: int, y: int)
  requires y > 0
  requires x >= 0
  ensures CeilingDivision(x, y) * y >= x
{
  var d := CeilingDivision(x, y);
  var q := x / y;
  var r := x % y;
  if r == 0 {
    assert d == q;
    assert d * y == x;
  } else {
    assert d == q + 1;
    assert q * y + r == x;
    assert r < y;
    assert q * y < x;
    assert (q + 1) * y = q * y + y > q * y + r = x;
  }
}

lemma MinStripsCorrect(a: int, b: int)
  requires ValidInput(a, b)
{
  var result := MinStripsNeeded(a, b);
  var m := a - 1;
  var k := b - 1;
  assert result >= 0;
  CeilingDivisionAtLeast(k, m);
  assert SocketsAfterStrips(result, a) >= b;
  if (result > 0) {
    if (k % m == 0) {
      assert SocketsAfterStrips(result - 1, a) < b;
    } else {
      assert SocketsAfterStrips(result - 1, a) < b;
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
  if b <= 1 {
    result := 0;
  } else {
    result := CeilingDivision(b - 1, a - 1);
  }
  MinStripsCorrect(a, b);
}
// </vc-code>

