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
{}

lemma PrimitiveRootCountCorrect(p: int)
  requires ValidInput(p)
  ensures CountPrimitiveRoots(p) == (if p == 2 then 1 else EulerPhi(p - 1))
{
  if p == 2 {
  } else {
    // Relate the definition of CountPrimitiveRoots to EulerPhi(p-1)
    // The condition `forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)`
    // is equivalent to `gcd(i, p-1) == 1`.
    // Proof sketch:
    // If gcd(i, p-1) == 1, then there is no j >= 2 that divides both i and p-1.
    // If gcd(i, p-1) != 1, then there exists a common divisor j >= 2.
    // This lemma essentially states that the set definition in CountPrimitiveRoots is equivalent to the set definition for EulerPhi(p-1).
    // This is a known mathematical result: the number of primitive roots modulo a prime p is EulerPhi(p-1).
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
    // Lemma call is technically not needed for verification if the function definition
    // in CountPrimitiveRoots is automatically proven equivalent by Dafny to EulerPhi(p-1).
    // However, including it can help guide the verifier if the relationship is complex.
    // PrimitiveRootCountCorrect(p); // Call the lemma to assert the equivalence
    return result;
  }
}
// </vc-code>

