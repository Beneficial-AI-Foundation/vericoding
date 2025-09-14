predicate ValidInput(N: int, A: int, B: int, C: int, D: int, E: int)
{
    N >= 1 && A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
}

function MinCapacity(A: int, B: int, C: int, D: int, E: int): int
    requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
{
    var temp1 := if A <= B then A else B;
    var temp2 := if temp1 <= C then temp1 else C;
    var temp3 := if temp2 <= D then temp2 else D;
    if temp3 <= E then temp3 else E
}

function CeilDiv(a: int, b: int): int
    requires a >= 0 && b >= 1
{
    (a + b - 1) / b
}

predicate CorrectResult(N: int, A: int, B: int, C: int, D: int, E: int, result: int)
    requires ValidInput(N, A, B, C, D, E)
{
    var minCap := MinCapacity(A, B, C, D, E);
    var groups := CeilDiv(N, minCap);
    result == 4 + groups
}

// <vc-helpers>
lemma MinCapacity_ge_1(A: int, B: int, C: int, D: int, E: int)
  requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
  ensures MinCapacity(A, B, C, D, E) >= 1
{
  var t1 := if A <= B then A else B;
  if A <= B {
    assert t1 == A;
  } else {
    assert t1 == B;
  }
  assert t1 >= 1;

  var t2 := if t1 <= C then t1 else C;
  if t1 <= C {
    assert t2 == t1;
  } else {
    assert t2 == C;
  }
  assert t2 >= 1;

  var t3 := if t2 <= D then t2 else D;
  if t2 <= D {
    assert t3 == t2;
  } else {
    assert t3 == D;
  }
  assert t3 >= 1;

  var t4 := if t3 <= E then t3 else E;
  if t3 <= E {
    assert t4 == t3;
  } else {
    assert t4 == E;
  }
  assert t4 >= 1;
}

lemma CeilDiv_ge_1(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures CeilDiv(a, b) >= 1
{
  assert a + b - 1 >= b;
  assert (a + b - 1) / b >= b / b;
  assert b / b == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: int, B: int, C: int, D: int, E: int) returns (result: int)
    requires ValidInput(N, A, B, C, D, E)
    ensures CorrectResult(N, A, B, C, D, E, result)
    ensures result >= 5
// </vc-spec>
// <vc-code>
{
  var minCap := MinCapacity(A, B, C, D, E);
  MinCapacity_ge_1(A, B, C, D, E);
  var groups := CeilDiv(N, minCap);
  CeilDiv_ge_1(N, minCap);
  result := 4 + groups;
}
// </vc-code>

