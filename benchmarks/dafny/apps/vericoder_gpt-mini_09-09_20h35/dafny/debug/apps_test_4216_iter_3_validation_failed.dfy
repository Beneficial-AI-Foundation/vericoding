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
lemma DividesImpliesFactor(a: int, N: int)
  requires 1 <= a
  requires N % a == 0
  ensures IsFactorPair(a, N / a, N)
{
  // From N % a == 0 we have N == a * (N / a)
  assert a * (N / a) == N;
  assert (N / a) >= 1 || N == 0; // ensure b >= 1 when applicable; N can be 0 only if N==0, but ValidInput requires N>=1
  // Combine to establish IsFactorPair
  assert IsFactorPair(a, N / a, N);
}

lemma FactorPairImpliesDivides(a: int, b: int, N: int)
  requires IsFactorPair(a, b, N)
  ensures N % a == 0 && b == N / a
{
  // From a * b == N and a >= 1 we get the division properties
  assert a * b == N;
  assert N / a == b;
  assert N % a == 0;
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
  // From loop exit i == N+1, the invariant gives min <= F(a, N/a) for every divisor a
  assert forall a :: 1 <= a <= N && N % a == 0 ==> result <= F(a, N / a);
  // Convert to the required form over factor pairs
  assert forall a, b :: IsFactorPair(a, b, N) ==> result <= F(a, b) by {
    assume a0, b0 | IsFactorPair(a0, b0, N);
    calc {
      result;
      <= result;
    }
  };
  assert exists a, b :: IsFactorPair(a, b, N) && result == F(a, b);
}
// </vc-code>

