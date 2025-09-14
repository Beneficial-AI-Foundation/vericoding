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
lemma numDigits_pos(n: int)
  requires n >= 1
  ensures numDigits(n) >= 1
{
}

lemma numDigits_monotone(n: int, m: int)
  requires 1 <= n <= m
  ensures numDigits(n) <= numDigits(m)
{
  if n < 10 {
    if m < 10 {
    } else {
      assert numDigits(m) >= 2 > 1 == numDigits(n);
    }
  } else {
    assert m >= n >= 10;
    assert numDigits(n) == 1 + numDigits(n / 10);
    assert numDigits(m) == 1 + numDigits(m / 10);
    assert n / 10 <= m / 10;
    numDigits_monotone(n / 10, m / 10);
  }
}

lemma factor_pair_exists(N: int)
  requires N >= 1
  ensures exists a, b :: IsFactorPair(a, b, N)
{
  var b := N;
  assert IsFactorPair(1, b, N);
}

lemma F_symmetric(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures F(a, b) == F(b, a)
{
}

lemma F_at_least_1(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures F(a, b) >= 1
{
}

lemma factor_pair_exists_for_a(N: int, a: int)
  requires N >= 1 && a >= 1 && N % a == 0
  ensures exists b :: IsFactorPair(a, b, N)
{
  var b := N / a;
  assert b >= 1;
  assert a * b == N;
}

lemma factor_pair_implies_b_positive(a: int, b: int, N: int)
  requires IsFactorPair(a, b, N)
  ensures b >= 1
{
}

lemma invariant_helper(N: int, a: int, best: int)
  requires N >= 1
  requires 1 <= a <= N + 1
  requires forall x :: 1 <= x < a && N % x == 0 && x <= N / x ==> best <= F(x, N/x)
  requires exists w1, w2 :: IsFactorPair(w1, w2, N) && best == F(w1, w2)
  ensures (exists b :: IsFactorPair(a, b, N)) ==> best <= F(a, N/a)
{
  if exists b :: IsFactorPair(a, b, N) {
    var b :| IsFactorPair(a, b, N);
    assert b == N / a;
    assert a <= N / a;
    assert best <= F(a, b);
  }
}

lemma minimal_value_lemma(N: int, best: int, witness_a: int, witness_b: int)
  requires N >= 1
  requires IsFactorPair(witness_a, witness_b, N) && best == F(witness_a, witness_b)
  requires forall a :: 1 <= a <= N && N % a == 0 && a <= N / a ==> best <= F(a, N/a)
  ensures forall a, b :: IsFactorPair(a, b, N) ==> best <= F(a, b)
{
  forall a, b | IsFactorPair(a, b, N)
    ensures best <= F(a, b)
  {
    if a <= b {
      assert N % a == 0;
      assert b == N / a;
      assert a <= N / a;
    } else {
      F_symmetric(a, b);
      assert F(a, b) == F(b, a);
      assert b <= a;
      assert N % b == 0;
      assert a == N / b;
      assert b <= N / b;
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
  var best := numDigits(N);
  var a := 1;
  var witness_a := 1;
  var witness_b := N;
  
  assert IsFactorPair(1, N, N);
  assert best == F(1, N);
  
  while (a <= N)
    invariant 1 <= a <= N + 1
    invariant IsFactorPair(witness_a, witness_b, N) && best == F(witness_a, witness_b)
    invariant forall x :: 1 <= x < a && N % x == 0 && x <= N / x ==> best <= F(x, N/x)
    decreases N - a
  {
    if N % a == 0 {
      var b := N / a;
      if b >= a {
        var current := F(a, b);
        if current < best {
          best := current;
          witness_a := a;
          witness_b := b;
        }
      }
    }
    a := a + 1;
  }
  
  minimal_value_lemma(N, best, witness_a, witness_b);
  result := best;
}
// </vc-code>

