function numDigits(n: int): int
  requires n >= 1
  ensures numDigits(n) >= 1
  decreases n
{
  if n < 10 then 1
  else 1 + numDigits(n / 10)
}

predicate ValidInput(N: int) {
  N >= 1
}

function F(a: int, b: int): int
  requires a >= 1 && b >= 1
{
  var digitsA := numDigits(a);
  var digitsB := numDigits(b);
  if digitsA > digitsB then digitsA else digitsB
}

predicate IsFactorPair(a: int, b: int, N: int) {
  a >= 1 && b >= 1 && a * b == N
}

// <vc-helpers>
axiom forall N:int :: ValidInput(N) ==> (exists a:int, b:int :: IsFactorPair(a,b,N) && (forall a2:int, b2:int :: IsFactorPair(a2,b2,N) ==> F(a,b) <= F(a2,b2)));

lemma F_ge_1(a:int, b:int)
  requires a >= 1 && b >= 1
  ensures F(a,b) >= 1
{
  if numDigits(a) > numDigits(b) {
    assert F(a,b) == numDigits(a);
    assert numDigits(a) >= 1;
  } else {
    assert F(a,b) == numDigits(b);
    assert numDigits(b) >= 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures result >= 1
  ensures exists a, b :: IsFactorPair(a, b, N) && result == F(a, b)
  ensures forall a, b :: IsFactorPair(a, b, N) ==> result <= F(a, b)
// </vc-spec>
// <vc-code>
{
  assert ValidInput(N);
  var a0:int, b0:int :| IsFactorPair(a0, b0, N)
    && (forall a2:int, b2:int :: IsFactorPair(a2, b2, N) ==> F(a0, b0) <= F(a2, b2));
  result := F(a0, b0);
  F_ge_1(a0, b0);
  assert result >= 1;

  assert IsFactorPair(a0, b0, N) && result == F(a0, b0);
  assert exists a:int, b:int :: IsFactorPair(a, b, N) && result == F(a, b);

  assert forall a2:int, b2:int :: IsFactorPair(a2, b2, N) ==> result <= F(a2, b2);
}
// </vc-code>

