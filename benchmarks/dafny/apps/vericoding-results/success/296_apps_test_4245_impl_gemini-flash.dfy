// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma LemmaCeilingDivisionPositive(x: int, y: int)
  requires x >= 0 && y > 0
  ensures x / y <= CeilingDivision(x, y)
  ensures x / y == CeilingDivision(x,y) || x / y + 1 == CeilingDivision(x,y)
{
  if x % y != 0 {
    assert x / y + 1 == CeilingDivision(x, y);
  }
}

lemma LemmaMinStripsNonNegative(a: int, b: int)
  requires ValidInput(a,b)
  ensures MinStripsNeeded(a,b) >= 0
{
  if b <= 1 {
    assert MinStripsNeeded(a,b) == 0;
  }
  else {
    assert b - 1 >= 0;
    assert a - 1 > 0;
    LemmaCeilingDivisionPositive(b - 1, a - 1);
    assert CeilingDivision(b - 1, a - 1) >= 0;
  }
}

lemma LemmaSocketsAfterStrips(strips: int, a: int)
  requires a > 1 && strips >= 0
  ensures SocketsAfterStrips(strips, a) == 1 + strips * (a - 1)
{
}

lemma LemmaMinStripsNeededImpliesCorrectResult(a: int, b: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, MinStripsNeeded(a, b))
{
  var m := MinStripsNeeded(a, b);
  
  LemmaMinStripsNonNegative(a, b);

  if b <= 1 {
    assert m == 0;
    assert SocketsAfterStrips(0, a) == 1;
    assert CorrectResult(a, b, 0);
  } else {
    var dividend := b - 1;
    var divisor := a - 1;
    
    assert dividend >= 0;
    assert divisor > 0;

    if dividend % divisor == 0 {
      assert m == dividend / divisor;
    } else {
      assert m == dividend / divisor + 1;
    }

    assert (m - 1) * divisor < dividend;
    assert m * divisor >= dividend;

    assert 1 + m * (a - 1) >= b;
    assert SocketsAfterStrips(m, a) >= b;

    if m > 0 {
      assert 1 + (m - 1) * (a - 1) < b;
      assert SocketsAfterStrips(m - 1, a) < b;
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
  LemmaMinStripsNeededImpliesCorrectResult(a, b);
}
// </vc-code>
