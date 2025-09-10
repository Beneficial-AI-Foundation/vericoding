predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
lemma GcdProperties(a: int, b: int)
  requires b > 0
  ensures gcd(a, b) == gcd(a % b, b)
  ensures gcd(a, b) == gcd(b, a % b)
{
}

function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a >= b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma SolvabilityLemma(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0)
{
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
  var a_mod_b := A % B;
  var g := gcd(a_mod_b, B);
  
  if C % g == 0 {
    SolvabilityLemma(A, B, C);
    result := "YES";
  } else {
    SolvabilityLemma(A, B, C);
    result := "NO";
  }
}
// </vc-code>

