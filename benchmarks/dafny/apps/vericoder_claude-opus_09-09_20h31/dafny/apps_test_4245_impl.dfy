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
lemma MinStripsCorrectness(a: int, b: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, MinStripsNeeded(a, b))
{
  var result := MinStripsNeeded(a, b);
  
  if b <= 1 {
    // If b <= 1, we need 0 strips (wall outlet is enough)
    assert result == 0;
    assert SocketsAfterStrips(0, a) == 1 >= b;
  } else {
    // b > 1, so we need strips
    var needed := b - 1;  // additional sockets needed beyond the wall outlet
    var perStrip := a - 1; // sockets added per strip
    
    assert result == CeilingDivision(needed, perStrip);
    
    // Prove that result strips give us at least b sockets
    if needed % perStrip == 0 {
      assert result == needed / perStrip;
      assert result * perStrip == needed;
      assert SocketsAfterStrips(result, a) == 1 + result * perStrip == 1 + needed == b;
    } else {
      assert needed >= 0;
      assert result == needed / perStrip + 1;
      assert result * perStrip > needed;
      assert SocketsAfterStrips(result, a) == 1 + result * perStrip > 1 + needed == b;
    }
    
    // Prove that (result - 1) strips would not be enough
    if result > 0 {
      assert (result - 1) * perStrip < needed;
      assert SocketsAfterStrips(result - 1, a) == 1 + (result - 1) * perStrip < 1 + needed == b;
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
  MinStripsCorrectness(a, b);
}
// </vc-code>

