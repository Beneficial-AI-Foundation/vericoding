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
_lemma SocketsAfterStripsNonDecreasing()
  ensures forall a: int, strips: int :: a > 1 && strips >= 0 ==> SocketsAfterStrips(strips, a) >= 1 + strips * (a - 1)

 corollary SocketsAfterStripsCorrect(strips: int, a: int, b: int)
  requires a > 1 && b >= 0 && strips >= 0
  ensures SocketsAfterStrips(strips, a) >= b <==> 1 + strips * (a - 1) >= b

 lemma CeilingDivisionIsCeil(x: int, y: int)
  requires y > 0
  ensures CeilingDivision(x, y) * y >= x &&
         (forall z: int :: z >= 0 && z * y >= x ==> z >= CeilingDivision(x, y))

 lemma CeilingDivisionProperties(x: int, y: int)
  requires y > 0
  ensures CeilingDivision(x, y) == if x % y == 0 then x / y else if x >= 0 then x / y + 1 else x / y
  ensures forall a: int, b: int :: a > 1 && b >= 0 && b > 1 ==> SocketsAfterStrips(CeilingDivision(b - 1, a - 1), a) >= b
  ensures forall a: int, b: int :: a > 1 && b >= 0 && b > 1 ==> CeilingDivision(b - 1, a - 1) > 0 ==> SocketsAfterStrips(CeilingDivision(b - 1, a - 1) - 1, a) < b
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

