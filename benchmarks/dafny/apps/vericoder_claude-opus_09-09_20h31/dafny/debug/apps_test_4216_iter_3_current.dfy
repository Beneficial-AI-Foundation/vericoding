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

lemma DivisorBoundProperty(N: int, d: int)
  requires N >= 1 && d >= 1 && N % d == 0
  ensures N / d >= 1 && d * (N / d) == N
{
  // Dafny can verify this automatically
}

lemma NumDigitsMonotonic(a: int, b: int)
  requires a >= 1 && b >= 1 && a <= b
  ensures numDigits(a) <= numDigits(b)
  decreases b
{
  if a == b {
    // trivial
  } else if b < 10 {
    assert a < 10;
    assert numDigits(a) == 1;
    assert numDigits(b) == 1;
  } else if a < 10 {
    assert numDigits(a) == 1;
    assert numDigits(b) >= 1;
  } else {
    assert a >= 10 && b >= 10;
    assert a / 10 >= 1 && b / 10 >= 1;
    assert a / 10 <= b / 10;
    NumDigitsMonotonic(a / 10, b / 10);
    assert numDigits(a / 10) <= numDigits(b / 10);
    assert numDigits(a) == 1 + numDigits(a / 10);
    assert numDigits(b) == 1 + numDigits(b / 10);
  }
}

lemma MinFactorPairProperty(N: int, optA: int, optB: int)
  requires N >= 1
  requires IsFactorPair(optA, optB, N)
  requires optA <= optB
  requires forall d :: 1 <= d < optA && N % d == 0 ==> d * d > N
  ensures forall a, b :: IsFactorPair(a, b, N) ==> F(optA, optB) <= F(a, b)
{
  forall a, b | IsFactorPair(a, b, N)
  ensures F(optA, optB) <= F(a, b)
  {
    if a <= b {
      // We need to show optA <= a and b <= optB won't work
      // Instead, we know that if a < optA, then a*a > N (by precondition)
      // So a * b = N > a * a, which means b > a, but we already have a <= b
      // This means if a < optA, then b > N/a > a, so b > sqrt(N)
      // And since optA * optB = N and optA is the largest divisor <= sqrt(N),
      // we have optB is the smallest divisor >= sqrt(N)
      
      if a < optA {
        assert a * a > N by { assert 1 <= a < optA && N % a == 0; }
        assert false by { assert a * b == N && a <= b && a * a > N; }
      }
      assert a >= optA;
      assert b <= optB by { assert a * b == N && optA * optB == N && a >= optA; }
      NumDigitsMonotonic(optB, b);
      assert numDigits(optB) <= numDigits(b);
      
      if numDigits(optA) > numDigits(optB) {
        assert F(optA, optB) == numDigits(optA);
        NumDigitsMonotonic(optA, a);
        assert numDigits(optA) <= numDigits(a);
        assert F(a, b) >= numDigits(a);
        assert F(optA, optB) <= F(a, b);
      } else {
        assert F(optA, optB) == numDigits(optB);
        assert F(a, b) >= numDigits(b);
        assert F(optA, optB) <= F(a, b);
      }
    } else {
      // a > b case
      if b < optA {
        assert b * b > N by { assert 1 <= b < optA && N % b == 0; }
        assert false by { assert a * b == N && b < a && b * b > N; }
      }
      assert b >= optA;
      assert a <= optB by { assert a * b == N && optA * optB == N && b >= optA; }
      NumDigitsMonotonic(optB, a);
      assert numDigits(optB) <= numDigits(a);
      
      if numDigits(optA) > numDigits(optB) {
        assert F(optA, optB) == numDigits(optA);
        NumDigitsMonotonic(optA, b);
        assert numDigits(optA) <= numDigits(b);
        assert F(a, b) >= numDigits(a);
        assert F(optA, optB) <= F(a, b);
      } else {
        assert F(optA, optB) == numDigits(optB);
        assert F(a, b) == numDigits(a);
        assert F(optA, optB) <= F(a, b);
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
  var i := 1;
  var bestA := 1;
  var bestB := N;
  
  while i * i <= N
    invariant 1 <= i <= N + 1
    invariant IsFactorPair(bestA, bestB, N)
    invariant bestA <= bestB
    invariant forall d :: 1 <= d < i && N % d == 0 ==> 
              (d <= bestA && N/d >= bestB)
    invariant forall d :: 1 <= d < bestA && N % d == 0 ==> d * d > N
  {
    if N % i == 0 {
      var j := N / i;
      assert i * j == N;
      
      if i <= j {
        bestA := i;
        bestB := j;
      }
    }
    i := i + 1;
  }
  
  assert forall d :: 1 <= d < bestA && N % d == 0 ==> d * d > N;
  MinFactorPairProperty(N, bestA, bestB);
  
  result := F(bestA, bestB);
}
// </vc-code>

