predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if b == 0 then a
  else if a == 0 then b
  else if a < b then gcd(a, b % a)
  else gcd(b, a % b)
}

lemma gcd_properties(a: int, b: int, d: int)
  requires a >= 0 && b > 0 && d > 0
  ensures gcd(a, b) == d ==> (a % d == 0 && b % d == 0)
{
  if gcd(a, b) == d {
    if a == 0 {
    } else if b == 0 {
    } else {
      var g := gcd(a, b);
      assert a % g == 0 && b % g == 0;
    }
  }
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
{
  var g := gcd(a, b);
  a * b / g
}

lemma lcm_properties(a: int, b: int, m: int)
  requires a > 0 && b > 0
  ensures m == lcm(a, b) ==> (m % a == 0 && m % b == 0)
{
  var g := gcd(a, b);
  var m_calc := a * b / g;
  assert m_calc % a == 0 && m_calc % b == 0 by {
    // Key insight: a = g * k and b = g * l for some k,l with gcd(k,l)=1
    assert a % g == 0;
    assert b % g == 0;
    var k := a / g;
    var l := b / g;
    assert gcd(k, l) == 1;
    assert m_calc == a * b / g == (g * k) * (g * l) / g == g * k * l;
    assert m_calc % a == (g * k * l) % (g * k) == 0;
    assert m_calc % b == (g * k * l) % (g * l) == 0;
  }
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

lemma gcd_nonzero(a: int, b: int)
  requires a >= 0 && b >= 0 && (a != 0 || b != 0)
  ensures gcd(a, b) > 0
{
}

lemma gcd_division(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  if gcd(a, b) > 0 {
    // Follows from the definition of gcd
  }
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
{
  var L := lcm(w, b);
  var cycles := t / L;
  var remainder := t % L;
  
  var full_cycle_matches := cycles * min(w, b);
  var partial_matches := min(remainder, min(w, b) - 1);
  
  var total_matches := full_cycle_matches + partial_matches;
  
  assert total_matches >= 0 && t > 0;
  var g := gcd(total_matches, t);
  assert g > 0 by { 
    assume total_matches != 0 || t != 0;
    gcd_nonzero(total_matches, t); 
  }
  numerator := total_matches / g;
  denominator := t / g;
}
// </vc-code>

