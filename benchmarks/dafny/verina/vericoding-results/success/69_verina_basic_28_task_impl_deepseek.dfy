// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

predicate isDivisible(n: nat, d: nat)
  requires d != 0
{
  n % d == 0
}

lemma NotPrimeImpliesFactor(n: nat)
  requires n >= 2
  requires !(forall k: nat :: 2 <= k < n ==> n % k != 0)
  ensures exists k: nat :: 2 <= k < n && n % k == 0
{
  // This lemma requires advanced induction; Dafny can often prove this automatically
}

// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  var i: nat := 2;
  result := true;
  while i < n
    invariant 2 <= i <= n
    invariant result ==> forall j: nat :: 2 <= j < i ==> n % j != 0
  {
    if n % i == 0 {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
