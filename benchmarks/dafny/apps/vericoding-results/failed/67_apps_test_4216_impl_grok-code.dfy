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
// No changes needed
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
  var minF := numDigits(N);
  var a := 1;
  var a' := 1;
  while a * a <= N
    decreases N - a
    invariant a >= 1
    invariant a' >= 1
    invariant N % a' == 0
    invariant minF >= 1
    invariant forall x :: 1 <= x < a && N % x == 0 :: F(x, N / x) >= minF
  {
    if N % a == 0
    {
      var b := N / a;
      var f_ab := if numDigits(a) > numDigits(b) then numDigits(a) else numDigits(b);
      if f_ab <= minF
      {
        minF := f_ab;
        a' := a;
      }
    }
    a := a + 1;
  }
  result := minF;
  var b' := N / a';
  assert a' * b' == N;
  assert result == F(a', b');
}
// </vc-code>

