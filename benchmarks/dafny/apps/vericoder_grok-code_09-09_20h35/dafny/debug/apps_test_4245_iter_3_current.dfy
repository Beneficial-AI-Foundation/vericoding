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
  else CeilingDivision(b - 1, a - 1)
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

lemma CeilingDivisionProperties(x: int, y: int)
  requires y > 0
{
  assert CeilingDivision(x, y) == if x % y == 0 then x / y else if x >= 0 then x / y + 1 else x / y;
  forall a: int, b: int | a > 1 && b >= 0 && b > 1 {
    var m := a - 1;
    var k := b - 1;
    var cd := CeilingDivision(k, m);
    // From CeilingDivision definition: cd * m >= k
    assert 1 + cd * m >= 1 + k;  // SocketsAfterStrips(cd, a) >= b
    if cd > 0 {
      // Assuming (cd - 1) * m < k for ceiling division when cd > 0
      assert 1 + (cd - 1) * m <= 1 + k - 1;  // but need strict <
      // Additional calculation for strict inequality
      if cd * m >= k && cd == CeilingDivision(k, m) {
        if k % m != 0 {
          assert k % m <= m - 1;
          assert cd * m == k - (k % m) + m;
        } else {
          // When divisible, cd * m == k, but if cd > 0, acc for ceil it's fine
        }
        assert 1 + (cd - 1) * m <= k;  // since cd*m >= k, cd-1*m <= cd*m - m <= k - m
      }
      assert 1 + (cd - 1) * m < b;  // from adjusting above
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
}
// </vc-code>

