function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma PrimeDivisor(n: nat)
  requires n > 1
  ensures exists p: nat :: Prime(p) && p <= n && n % p == 0
{
  var i: nat := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant forall k: nat | 2 <= k < i :: n % k != 0
  {
    if n % i == 0 {
      assert n % i == 0;
      assert i <= n;
      assert Prime(i) by {
        assert forall k: nat | 1 < k < i :: n % k != 0;
        assert forall k: nat | 1 < k < i :: i % k != 0;
      }
      return;
    }
    i := i + 1;
  }
}

ghost function Helpers_PrimeFactors(n: nat): set<nat>
  requires n > 1
  ensures forall p :: p in Helpers_PrimeFactors(n) ==> Prime(p) && n % p == 0
  ensures exists prod: nat :: prod == multiply_set(Helpers_PrimeFactors(n)) && prod == n
{
  if Prime(n) then {n} 
  else
    var p: nat :| Prime(p) && p <= n && n % p == 0;
    var quotient: nat := n / p;
    {p} + Helpers_PrimeFactors(quotient)
}

ghost function multiply_set(s: set<nat>): nat
  decreases s
{
  if s == {} then 1
  else
    var x :| x in s;
    x * multiply_set(s - {x})
}

lemma MultiplySetLemma(s: set<nat>, n: nat)
  requires n in s
  ensures multiply_set(s) == n * multiply_set(s - {n})
{
}

lemma PrimeFactorsCorrect(n: nat)
  requires n > 1
  ensures multiply_set(Helpers_PrimeFactors(n)) == n
  decreases n
{
  if Prime(n) {
  } else {
    var p: nat :| Prime(p) && p <= n && n % p == 0;
    var quotient: nat := n / p;
    PrimeFactorsCorrect(quotient);
    MultiplySetLemma(Helpers_PrimeFactors(n), p);
  }
}

lemma PrimeFactorsPrime(n: nat)
  requires n > 1
  ensures forall p :: p in Helpers_PrimeFactors(n) ==> Prime(p) && n % p == 0
{
}

lemma PrimeFactorsCount(n: nat)
  requires n > 1
  ensures |Helpers_PrimeFactors(n)| >= 1
{
}

lemma MultiplySetThreePrimes(n: nat)
  requires n > 1
  ensures |Helpers_PrimeFactors(n)| == 3 ==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && n == a * b * c
{
  var factors := Helpers_PrimeFactors(n);
  if |factors| == 3 {
    var a :| a in factors;
    var rem1 := factors - {a};
    var b :| b in rem1;
    var rem2 := rem1 - {b};
    var c :| c in rem2;
    assert rem2 == {c};
    assert factors == {a, b, c};
    assert multiply_set(factors) == a * b * c;
    assert multiply_set(factors) == n;
  }
}

lemma NotThreePrimesImpliesNotThreeFactors(n: nat)
  requires n > 1
  ensures (forall a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && n == a * b * c ==> |Helpers_PrimeFactors(n)| == 3)
{
}

lemma ThreeFactorsImpliesThreePrimes(n: nat)
  requires n > 1
  ensures |Helpers_PrimeFactors(n)| == 3 ==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && n == a * b * c
{
  MultiplySetThreePrimes(n);
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var factors: set<nat> := Helpers_PrimeFactors(x);
  var count: nat := |factors|;
  
  if count == 3 {
    ans := true;
    ThreeFactorsImpliesThreePrimes(x);
  } else {
    ans := false;
    assert !(exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c) by {
      if exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c {
        NotThreePrimesImpliesNotThreeFactors(x);
        assert |factors| == 3;
        assert count == 3;
      }
    }
  }
}
// </vc-code>

