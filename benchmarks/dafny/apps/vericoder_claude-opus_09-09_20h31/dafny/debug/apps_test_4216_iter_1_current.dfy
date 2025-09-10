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

lemma MinFactorPairProperty(N: int, optA: int, optB: int)
  requires N >= 1
  requires IsFactorPair(optA, optB, N)
  requires optA <= optB
  requires forall d :: 1 <= d <= optA && N % d == 0 ==> d <= optA
  ensures forall a, b :: IsFactorPair(a, b, N) ==> F(optA, optB) <= F(a, b)
{
  forall a, b | IsFactorPair(a, b, N)
  ensures F(optA, optB) <= F(a, b)
  {
    if a <= b {
      assert a <= optA <= optB <= b;
      assert numDigits(optB) <= numDigits(b);
      assert F(optA, optB) <= numDigits(b);
      assert F(a, b) >= numDigits(b);
    } else {
      assert b <= optA <= optB <= a;
      assert numDigits(optB) <= numDigits(a);
      assert F(optA, optB) <= numDigits(a);
      assert F(a, b) >= numDigits(a);
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
    invariant 1 <= i <= N
    invariant IsFactorPair(bestA, bestB, N)
    invariant bestA <= bestB
    invariant forall d :: 1 <= d < i && N % d == 0 ==> 
              (d <= bestA && N/d >= bestB) || (d * d > N)
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
  
  assert forall d :: 1 <= d <= bestA && N % d == 0 ==> d <= bestA;
  MinFactorPairProperty(N, bestA, bestB);
  
  result := F(bestA, bestB);
}
// </vc-code>

