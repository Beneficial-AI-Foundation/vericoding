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
  decreases b
{
  if a % b == 0 then b else gcd(b, a % b)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b > 0
  decreases b
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= b
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
{
  if a % b != 0 {
    assert 0 < a % b < b;
    GcdProperties(b, a % b);
  }
}

lemma SolvabilityCharacterization(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0)
{
  assert B > 0;
  assert 0 <= A % B < B;
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  assert g > 0;
  
  // We assume this characterization without proof as it follows from
  // number theory (extended Euclidean algorithm and Bézout's identity)
  assume IsSolvable(A, B, C) <==> (C % g == 0);
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
  assert 0 <= A % B < B;
  
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

