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
  requires a >= 0 && b > 0
  decreases a, b
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
    // This lemma needs more detailed proof
    if a == 0 {
    } else if b == 0 {
    } else {
      var g := gcd(a, b);
      // Key insight: gcd(a, b) divides both a and b
      assert a % g == 0 && b % g == 0 by {
        if a < b {
          assert gcd(a, b) == gcd(a, b % a);
        } else {
          assert gcd(a, b) == gcd(b, a % b);
        }
      }
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
    assert exists k: int :: a == g * k && b == g * (b / g);
    assert m_calc == a * b / g == g * k * (g * (b / g)) / g == g * k * (b / g);
    assert m_calc % a == (g * k * (b / g)) % (g * k) == 0;
    assert m_calc % b == (g * k * (b / g)) % (g * (b / g)) == 0;
  }
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

lemma gcd_nonzero(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma gcd_division(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
}
// </vc-helpers>
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
  
  // Ensure gcd is called with valid arguments
  assert total_matches >= 0 && t > 0;
  var g := gcd(total_matches, t);
  assert g > 0 by { gcd_nonzero(total_matches, t); }
  numerator := total_matches / g;
  denominator := t / g;
}
// </vc-code>

