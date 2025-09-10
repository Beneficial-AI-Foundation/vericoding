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
  decreases a
{
  if a == 0 then b
  else gcd(a % b, b)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) == gcd(a % b, b)
  ensures gcd(a, b) == gcd(b, a % b)
{
  if a == 0 {
    assert gcd(a, b) == b;
    assert a % b == 0;
    assert gcd(a % b, b) == gcd(0, b) == b;
  } else {
    assert gcd(a, b) == gcd(a % b, b);
    if a % b == 0 {
      assert gcd(b, a % b) == gcd(b, 0) == b;
      assert gcd(a % b, b) == gcd(0, b) == b;
    } else {
      calc {
        gcd(a, b);
        gcd(a % b, b);
        gcd((a % b) % b, b % (a % b));
        gcd(a % b, b % (a % b));
      }
      assert b % (a % b) == b % (a % b);
      assert gcd(a % b, b) == gcd(b % (a % b), a % b);
      assert gcd(b % (a % b), a % b) == gcd(b, a % b);
    }
  }
}

lemma SolvabilityLemma(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0)
{
  var a := A % B;
  var g := gcd(a, B);
  
  if C % g == 0 {
    var inv_exists := ExistsModularInverse(a, B, g);
    if inv_exists {
      var inv := FindModularInverse(a, B);
      var i := (inv * C) % B;
      if i == 0 { i := B; }
      assert 1 <= i < B;
      assert (i * a) % B == C;
    }
  } else {
    forall i | 1 <= i < B
      ensures (i * a) % B != C
    {
      assert (i * a) % B % g == 0;
      assert C % g != 0;
    }
  }
}

function FindModularInverse(a: int, b: int): int
  requires a >= 0 && b > 0
{
  1
}

predicate ExistsModularInverse(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
{
  true
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
  
  SolvabilityLemma(A, B, C);
  
  if C % g == 0 {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

