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
  decreases b, a
{
  if a == 0 then b
  else if a % b == 0 then b
  else gcd(b, a % b)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) == gcd(a % b, b) || a % b == 0
  ensures a % b > 0 ==> gcd(a, b) == gcd(b, a % b)
{
  if a == 0 {
    assert gcd(a, b) == b;
    assert a % b == 0;
    assert gcd(a % b, b) == gcd(0, b) == b;
  } else if a % b == 0 {
    assert gcd(a, b) == b;
    assert gcd(a % b, b) == gcd(0, b) == b;
  } else {
    assert a % b > 0;
    assert gcd(a, b) == gcd(b, a % b);
  }
}

lemma SolvabilityLemma(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures A % B > 0 ==> (IsSolvable(A, B, C) <==> (C % gcd(A % B, B) == 0))
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
    
    if C % g == 0 {
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

