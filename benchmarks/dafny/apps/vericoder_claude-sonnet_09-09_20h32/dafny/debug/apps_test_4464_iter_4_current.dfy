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
  else gcd(b % a, a)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a > 0 ==> gcd(a, b) == gcd(b % a, a)
  ensures a == 0 ==> gcd(a, b) == b
{
  if a == 0 {
    assert gcd(a, b) == b;
  } else {
    assert gcd(a, b) == gcd(b % a, a);
  }
}

lemma SolvabilityLemma(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  requires B > 0
  ensures A % B > 0 ==> (IsSolvable(A, B, C) <==> (gcd(A % B, B) > 0 && C % gcd(A % B, B) == 0))
  ensures A % B == 0 ==> (IsSolvable(A, B, C) <==> C == 0)
{
  var a := A % B;
  if a == 0 {
    if C == 0 {
      assert (1 * 0) % B == 0 == C;
      assert IsSolvable(A, B, C);
    } else {
      forall i | 1 <= i < B
        ensures (i * a) % B != C
      {
        assert (i * 0) % B == 0;
        assert C != 0;
      }
      assert !IsSolvable(A, B, C);
    }
  } else {
    var g := gcd(a, B);
    assert g > 0;
    if g > 0 && C % g == 0 {
      var i := 1;
      assert 1 <= i < B;
      if (i * a) % B == C {
        assert IsSolvable(A, B, C);
      }
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
  
  if a_mod_b == 0 {
    if C == 0 {
      result := "YES";
    } else {
      result := "NO";
    }
  } else {
    var g := gcd(a_mod_b, B);
    
    SolvabilityLemma(A, B, C);
    
    if g > 0 && C % g == 0 {
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

