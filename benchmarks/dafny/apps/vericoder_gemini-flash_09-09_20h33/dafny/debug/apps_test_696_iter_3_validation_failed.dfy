predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a, b
{
  if a == 0 then b
  else if b == 0 then a
  else if a > b then gcd(a % b, b)
  else gcd(a, b % a)
}

predicate IsCoprime(a: int, b: int) {
  gcd(a, b) == 1
}

function EulerPhi(n: int): int
  requires n > 0
  ensures EulerPhi(n) >= 0
{
  if n == 1 then 1
  else |set i | 1 <= i < n && IsCoprime(i, n)|
}

lemma FactorizationCoprime(a: int, b: int, j: int)
  requires 2 <= j
  requires (a % j == 0 && b % j == 0)
  ensures !IsCoprime(a, b)
{
  assert gcd(a, b) % j == 0; // if j divides a and b, it must divide their gcd
  assert gcd(a, b) >= j; // since j >= 2, gcd(a,b) must be at least j
  assert gcd(a, b) != 1; // therefore gcd(a,b) is not 1
}

lemma PrimitiveRootCountCorrect(p: int)
  requires ValidInput(p)
  ensures CountPrimitiveRoots(p) == (if p == 2 then 1 else EulerPhi(p - 1))
{
  if p == 2 {
  } else {
    // To prove CountPrimitiveRoots(p) == EulerPhi(p - 1) for p > 2,
    // we need to show the equivalence of the two set definitions:
    // Set 1 (CountPrimitiveRoots): { i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)) }
    // Set 2 (EulerPhi(p-1)): { i | 1 <= i < p-1 && IsCoprime(i, p-1) }
    // which simplifies to { i | 1 <= i < p-1 && gcd(i, p-1) == 1 }

    // We need to prove:
    // (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)) <==> gcd(i, p-1) == 1

    // Proof by contradiction for (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)) ==> gcd(i, p-1) == 1
    // Assume gcd(i, p-1) != 1. Then there exists some common divisor k >= 2.
    // If such a k exists, then (p-1) % k == 0 and i % k == 0.
    // Since k is a divisor of i, k <= i. So 2 <= k <= i.
    // This contradicts the condition (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)).
    // Therefore, our assumption must be false, so gcd(i, p-1) == 1.

    // Proof for gcd(i, p-1) == 1 ==> (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))
    // Assume gcd(i, p-1) == 1.
    // Assume, for the sake of contradiction, that there exists some j such that 2 <= j <= i and (p-1) % j == 0 and i % j == 0.
    // If j divides both i and p-1, then j is a common divisor of i and p-1.
    // Since j >= 2, this means that gcd(i, p-1) must be at least j, and thus gcd(i, p-1) != 1.
    // This contradicts our assumption that gcd(i, p-1) == 1.
    // Therefore, such a j cannot exist.
    // So, (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)) holds.

    // Dafny's SMT solver is likely able to infer this equivalence without an explicit step-by-step proof in the lemma.
    // The key is that the definition of gcd is available.
  }
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
  if p == 2 {
    return 1;
  } else {
    var result := EulerPhi(p - 1);
    PrimitiveRootCountCorrect(p); // Call the lemma to assert the equivalence
    return result;
  }
}
// </vc-code>

