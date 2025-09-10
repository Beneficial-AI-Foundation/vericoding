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
  ensures forall a, b :: IsFactorPair(a, b, N) && (a < 1) ==> F(1, N) <= F(a, b)
{
}

lemma FactorPairProperties(N: int, a: int, b: int)
  requires N >= 1 && IsFactorPair(a, b, N)
  ensures a >= 1 && b >= 1
  ensures a * b == N
{
}

lemma AllFactorPairsConsidered(N: int, i: int)
  requires N >= 1 && i >= 1 && i * i > N
  ensures forall a, b :: IsFactorPair(a, b, N) ==> (a < i || a * a > N)
{
  forall a, b | IsFactorPair(a, b, N)
    ensures a < i || a * a > N
  {
    if a >= i {
      assert a * b == N;
      assert a >= i;
      assert i * i > N;
      assert a * a >= i * i > N;
    }
  }
}

lemma LoopInvariantMaintained(N: int, i: int, minF: int)
  requires N >= 1 && i >= 1
  requires exists a, b :: IsFactorPair(a, b, N) && minF == F(a, b)
  requires forall a, b :: IsFactorPair(a, b, N) && (a < i || (a >= i && a * a > N)) ==> minF <= F(a, b)
  requires N % i == 0
  ensures forall a, b :: IsFactorPair(a, b, N) && (a < i + 1 || (a >= i + 1 && a * a > N)) ==> minF <= F(a, b)
{
  FactorPairFromDivisor(N, i);
  forall a, b | IsFactorPair(a, b, N) && (a < i + 1 || (a >= i + 1 && a * a > N))
    ensures minF <= F(a, b)
  {
    if a < i || (a >= i && a * a > N) {
      assert minF <= F(a, b);
    } else if a == i {
      assert N % i == 0;
      assert IsFactorPair(i, N / i, N);
      assert minF <= F(i, N / i);
      assert F(i, N / i) == F(a, b) by {
        assert a == i && b == N / i;
      }
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
  
  AllFactorPairsConsidered(N, i);
  result := minF;
}
// </vc-code>

