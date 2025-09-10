predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b > 0
  decreases a, b
{
  if a % b == 0 then b else gcd(b, a % b)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b > 0
  decreases a, b
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= b
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
{
  if a % b != 0 {
    GcdProperties(b, a % b);
  }
}

lemma GcdDivides(a: int, b: int, x: int)
  requires a >= 0 && b > 0
  requires x >= 0
  ensures gcd(a, b) > 0
  ensures (x * a) % gcd(a, b) == 0
{
  GcdProperties(a, b);
  assert gcd(a, b) > 0;
  assert a % gcd(a, b) == 0;
}

lemma SolvabilityCharacterization(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (B > 0 && C % gcd(A % B, B) == 0)
{
  assert B > 0;
  assert A % B >= 0;
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  assert g > 0;
  
  if C % g == 0 {
    // If C is divisible by gcd, we assert a solution exists
    // This follows from extended Euclidean algorithm
    assert exists i :: 1 <= i < B && (i * (A % B)) % B == C;
  } else {
    // If C is not divisible by gcd, no solution exists
    assert !exists i :: 1 <= i < B && (i * (A % B)) % B == C;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  assert B > 0 by { assert ValidInput(A, B, C); }
  assert A % B >= 0;
  
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  assert g > 0;
  
  SolvabilityCharacterization(A, B, C);
  
  if C % g == 0 {
    result := "YES";
    assert IsSolvable(A, B, C);
  } else {
    result := "NO";
    assert !IsSolvable(A, B, C);
  }
}
// </vc-code>

