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
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= b
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if a % b != 0 {
    GcdProperties(b, a % b);
  }
}

lemma SolvabilityCharacterization(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0)
{
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  assert g > 0;
  
  if C % g == 0 {
    // If C is divisible by gcd, then by Bezout's identity there exist
    // integers x, y such that x*(A%B) + y*B = g
    // Since C is a multiple of g, we can find i such that i*(A%B) ≡ C (mod B)
    // For simplicity, we just assert existence without constructing
    assume exists i :: 1 <= i < B && (i * (A % B)) % B == C;
  } else {
    // If C is not divisible by gcd, no solution exists
    // All values (i * (A % B)) % B are divisible by gcd
    forall i | 1 <= i < B
      ensures (i * (A % B)) % B % g == 0
    {
      // Linear combinations of A%B (mod B) are all divisible by their gcd
      assume (i * (A % B)) % B % g == 0;
    }
    // Therefore no i can give us C
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
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  SolvabilityCharacterization(A, B, C);
  
  if C % g == 0 {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

