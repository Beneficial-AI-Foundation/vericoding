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
// No helpers needed for this proof.
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
  var bestA := 1;
  var bestB := N;
  var min := F(1, N);
  var i := 2;
  while i <= N
    invariant 1 <= i <= N + 1
    invariant IsFactorPair(bestA, bestB, N) && min == F(bestA, bestB)
    invariant forall a :: 1 <= a < i && N % a == 0 ==> min <= F(a, N / a)
    decreases N - i + 1
  {
    if N % i == 0 {
      var b := N / i;
      var f := F(i, b);
      if f < min {
        min := f;
        bestA := i;
        bestB := b;
      }
    }
    i := i + 1;
  }
  result := min;
  assert IsFactorPair(bestA, bestB, N) && result == F(bestA, bestB);
  assert exists a, b :: IsFactorPair(a, b, N) && result == F(a, b);
  assert forall a, b :: IsFactorPair(a, b, N) ==> result <= F(a, b);
}
// </vc-code>

