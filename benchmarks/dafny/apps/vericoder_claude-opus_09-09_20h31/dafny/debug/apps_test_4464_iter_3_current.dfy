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
{
  if a % b != 0 {
    GcdProperties(b, a % b);
  }
}

lemma GcdDivides(a: int, b: int, x: int)
  requires a >= 0 && b > 0
  requires x >= 0
  ensures (x * a) % gcd(a, b) == 0
{
  GcdProperties(a, b);
}

lemma SolvabilityCharacterization(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0)
{
  var g := gcd(A % B, B);
  GcdProperties(A % B, B);
  
  if C % g == 0 {
    // If C is divisible by gcd, a solution exists
    // We can find an i such that (i * (A % B)) % B == C
    // This is guaranteed by Bezout's identity
    var found := false;
    var i := 1;
    while i < B && !found
      invariant 1 <= i <= B
      decreases B - i
    {
      if (i * (A % B)) % B == C {
        found := true;
        break;
      }
      i := i + 1;
    }
  }
  
  if !IsSolvable(A, B, C) {
    // If no solution exists, C cannot be divisible by gcd
    forall i | 1 <= i < B
      ensures (i * (A % B)) % B != C
    {
      if C % g != 0 {
        GcdDivides(A % B, B, i);
      }
    }
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

