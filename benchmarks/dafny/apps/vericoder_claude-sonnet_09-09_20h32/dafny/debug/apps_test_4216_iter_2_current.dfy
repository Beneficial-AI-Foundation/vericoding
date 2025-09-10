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
lemma FactorPairExists(N: int)
  requires N >= 1
  ensures exists a, b :: IsFactorPair(a, b, N)
{
  assert IsFactorPair(1, N, N);
}

lemma FactorPairSymmetric(a: int, b: int, N: int)
  requires IsFactorPair(a, b, N)
  ensures IsFactorPair(b, a, N)
{
}

lemma FSymmetric(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures F(a, b) == F(b, a)
{
}

lemma SquareRootBound(N: int, a: int, b: int)
  requires N >= 1 && IsFactorPair(a, b, N) && a <= b
  ensures a * a <= N
{
}

lemma FactorPairFromDivisor(N: int, a: int)
  requires N >= 1 && a >= 1 && N % a == 0
  ensures IsFactorPair(a, N / a, N)
{
}

lemma InitialInvariant(N: int)
  requires N >= 1
  ensures forall a, b :: IsFactorPair(a, b, N) && (a < 1 || (a >= 1 && a * a > N)) ==> F(1, N) <= F(a, b)
{
  forall a, b | IsFactorPair(a, b, N) && (a < 1 || (a >= 1 && a * a > N))
    ensures F(1, N) <= F(a, b)
  {
    if a >= 1 && a * a > N {
      assert a * b == N;
      assert a > 0 && b > 0;
      assert a * a > N == a * b;
      assert a > b;
      assert F(a, b) >= numDigits(a);
      assert F(1, N) <= numDigits(N);
      assert numDigits(a) >= 1;
    }
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
  var minF := F(1, N);
  InitialInvariant(N);
  var i := 1;
  
  while i * i <= N
    invariant i >= 1
    invariant minF >= 1
    invariant exists a, b :: IsFactorPair(a, b, N) && minF == F(a, b)
    invariant forall a, b :: IsFactorPair(a, b, N) && (a < i || (a >= i && a * a > N)) ==> minF <= F(a, b)
    decreases N - i * i + 1
  {
    if N % i == 0 {
      FactorPairFromDivisor(N, i);
      var factor1 := i;
      var factor2 := N / i;
      var currentF := F(factor1, factor2);
      if currentF < minF {
        minF := currentF;
      }
    }
    i := i + 1;
  }
  
  result := minF;
}
// </vc-code>

