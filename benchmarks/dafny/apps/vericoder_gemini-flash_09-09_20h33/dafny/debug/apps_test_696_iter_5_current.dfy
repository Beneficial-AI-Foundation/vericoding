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
  // If j divides both a and b, then gcd(a, b) must be at least j.
  // Since j >= 2, gcd(a, b) must be greater than 1, so a and b are not coprime.
  assert gcd(a, b) % j == 0 by {
    var g := gcd(a, b);
    if g == 0 {
      // If g is 0, it means a and b are both 0. But a,b >= 0 and j >= 2, so this path is not relevant here.
    } else {
      assert j <= g; // If j divides both a and b, then j must be a common divisor. The greatest common divisor must be at least as large as j.
    }
  }
  assert gcd(a, b) != 1;
}

lemma PrimitiveRootsEquiv(p_minus_1: int)
  requires p_minus_1 >= 1
  ensures (forall i :: 1 <= i < p_minus_1 ==> ((forall j :: 2 <= j <= i ==> !((p_minus_1) % j == 0 && i % j == 0)) <==> IsCoprime(i, p_minus_1)))
{
  forall i | 1 <= i < p_minus_1
  ensures ((forall j :: 2 <= j <= i ==> !((p_minus_1) % j == 0 && i % j == 0)) <==> IsCoprime(i, p_minus_1))
  {
    assert (forall j :: 2 <= j <= i ==> !((p_minus_1) % j == 0 && i % j == 0)) <==> (gcd(i, p_minus_1) == 1);
  }
}

lemma PrimitiveRootCountCorrect(p: int)
  requires ValidInput(p)
  ensures CountPrimitiveRoots(p) == (if p == 2 then 1 else EulerPhi(p - 1))
{
  if p == 2 {
    // If p == 2, CountPrimitiveRoots(2) is 1.
    // EulerPhi(2-1) = EulerPhi(1) = 1.
    // So both sides equal 1.
  } else {
    // We need to show that the set defined in CountPrimitiveRoots for p > 2
    // |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
    // is equal to the set defined for EulerPhi(p-1)
    // |set i | 1 <= i < p-1 && IsCoprime(i, p-1)|.
    // This is shown by the PrimitiveRootsEquiv lemma.
    PrimitiveRootsEquiv(p - 1);
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
    // The postcondition `result == CountPrimitiveRoots(p)` needs to be established.
    // Based on the `PrimitiveRootCountCorrect` lemma, we know `CountPrimitiveRoots(p) == EulerPhi(p-1)`.
    // Since `result` is assigned `EulerPhi(p-1)`, the postcondition follows directly.
    PrimitiveRootCountCorrect(p); // Call the lemma to inform Dafny about the equivalence
    return result;
  }
}
// </vc-code>

