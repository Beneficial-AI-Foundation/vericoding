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
lemma MinStripsNeededCorrect(a: int, b: int)
  requires ValidInput(a, b)
  ensures MinStripsNeeded(a, b) >= 0
  ensures SocketsAfterStrips(MinStripsNeeded(a, b), a) >= b
  ensures MinStripsNeeded(a, b) == 0 || SocketsAfterStrips(MinStripsNeeded(a, b) - 1, a) < b
{
  if b <= 1 {
    assert MinStripsNeeded(a, b) == 0;
    assert SocketsAfterStrips(0, a) == 1 >= b;
  } else {
    var n := CeilingDivision(b - 1, a - 1);
    assert MinStripsNeeded(a, b) == n;
    
    // Prove SocketsAfterStrips(n, a) >= b
    var sockets := SocketsAfterStrips(n, a);
    assert sockets == 1 + n * (a - 1);
    
    // From ceiling division definition
    if (b - 1) % (a - 1) == 0 {
      assert n == (b - 1) / (a - 1);
      assert sockets == 1 + (b - 1) == b;
    } else {
      assert n == (b - 1) / (a - 1) + 1;
      assert sockets == 1 + ((b - 1) / (a - 1) + 1) * (a - 1);
      assert sockets >= 1 + ((b - 1) / (a - 1) + 1) * (a - 1) - (a - 2);
      assert sockets >= b;
    }
    
    // Prove SocketsAfterStrips(n - 1, a) < b
    if n > 0 {
      var prev_sockets := SocketsAfterStrips(n - 1, a);
      assert prev_sockets == 1 + (n - 1) * (a - 1);
      
      // From ceiling division definition
      assert n - 1 == (b - 1) / (a - 1);
      assert prev_sockets == 1 + ((b - 1) / (a - 1)) * (a - 1);
      assert prev_sockets <= 1 + (b - 1) - 1;
      assert prev_sockets < b;
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

