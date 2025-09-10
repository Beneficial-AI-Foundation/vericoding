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
lemma SocketsAfterStripsMonotonic(strips1: int, strips2: int, a: int)
  requires a > 1 && strips1 >= 0 && strips2 >= strips1
  ensures SocketsAfterStrips(strips1, a) <= SocketsAfterStrips(strips2, a)
{
  if strips1 == strips2 {
  } else {
    SocketsAfterStripsMonotonic(strips1, strips2 - 1, a);
  }
}

lemma CeilingDivisionCorrect(x: int, y: int)
  requires y > 0 && x >= 0
  ensures (x - 1) / y < CeilingDivision(x, y) * y
  ensures CeilingDivision(x, y) * y >= x
{
  if x % y == 0 {
    assert CeilingDivision(x, y) == x / y;
    assert CeilingDivision(x, y) * y == x;
  } else {
    assert x >= 0;
    assert CeilingDivision(x, y) == x / y + 1;
    assert CeilingDivision(x, y) * y == (x / y + 1) * y;
    assert CeilingDivision(x, y) * y == x / y * y + y;
    assert x / y * y <= x < (x / y + 1) * y;
    assert CeilingDivision(x, y) * y >= x;
    assert (x - 1) / y <= x / y;
    assert (x - 1) / y < x / y + 1;
    assert (x - 1) / y < CeilingDivision(x, y);
    assert (x - 1) / y * y < CeilingDivision(x, y) * y;
  }
}

lemma MinStripsNeededCorrect(a: int, b: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, MinStripsNeeded(a, b))
{
  var result := MinStripsNeeded(a, b);
  
  if b <= 1 {
  } else {
    assert result == CeilingDivision(b - 1, a - 1);
    CeilingDivisionCorrect(b - 1, a - 1);
    
    assert SocketsAfterStrips(result, a) == 1 + result * (a - 1);
    assert result * (a - 1) >= b - 1;
    assert SocketsAfterStrips(result, a) >= b;
    
    if result > 0 {
      assert (result - 1) * (a - 1) < b - 1;
      assert SocketsAfterStrips(result - 1, a) == 1 + (result - 1) * (a - 1);
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
  result := MinStripsNeeded(a, b);
  MinStripsNeededCorrect(a, b);
}
// </vc-code>

