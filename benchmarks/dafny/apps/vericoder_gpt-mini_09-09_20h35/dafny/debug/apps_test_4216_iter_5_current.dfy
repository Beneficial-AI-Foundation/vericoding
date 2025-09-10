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
lemma DividesImpliesProduct(i: int, N: int)
  requires N >= 0 && i > 0 && N % i == 0
  ensures i * (N / i) == N
{
  // By the division algorithm: N == i * (N / i) + N % i
  assert N == i * (N / i) + N % i;
  assert N % i == 0;
  assert N == i * (N / i) + 0;
  assert i * (N / i) == N;
}

lemma FactorPairLe(a: int, b: int, N: int)
  requires IsFactorPair(a, b, N)
  ensures a <= N && b <= N
{
  // From b >= 1 we get a*(b-1) >= 0, hence a <= a*b = N
  assert b - 1 >= 0;
  assert a * (b - 1) >= 0;
  assert a * b - a == a * (b - 1);
  assert a * b - a >= 0;
  assert a <= a * b;
  assert a * b == N;
  assert a <= N;

  // Symmetrically for b
  assert a - 1 >= 0;
  assert b * (a - 1) >= 0;
  assert a * b - b == b * (a - 1);
  assert a * b - b >= 0;
  assert b <= a * b;
  assert b <= N;
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
    invariant forall a, b :: IsFactorPair(a, b, N) && a < i ==> min <= F(a, b)
    decreases N - i + 1
  {
    if N % i == 0 {
      var b := N / i;
      // establish that (i, b) is a factor pair
      DividesImpliesProduct(i, N);
      var f := F(i, b);
      if f < min {
        min := f;
        bestA := i;
        bestB := b;
      }
    }
    i := i + 1;
  }
  // At loop exit i == N + 1
  assert i == N + 1;
  result := min;
  assert IsFactorPair(bestA, bestB, N) && result == F(bestA, bestB);
  assert exists a, b :: IsFactorPair(a, b, N) && result == F(a, b);
  // Use the invariant (with i == N+1) to conclude minimality over all factor pairs
  assert forall a, b :: IsFactorPair(a, b, N) ==> result <= F(a, b);
}
// </vc-code>

