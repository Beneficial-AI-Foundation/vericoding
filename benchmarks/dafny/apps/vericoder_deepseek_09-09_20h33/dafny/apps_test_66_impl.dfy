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
  if a == 0 then b
  else gcd(b % a, a)
}

lemma gcd_properties(a: int, b: int, d: int)
  requires a >= 0 && b > 0 && d > 0
  ensures gcd(a, b) == d ==> (a % d == 0 && b % d == 0)
{
  if gcd(a, b) == d {
    var g := gcd(a, b);
    if a == 0 {
    } else {
      gcd_division(a, b);
    }
  }
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
{
  var g := gcd(a, b);
  a * (b / g)
}

lemma lcm_properties(a: int, b: int, m: int)
  requires a > 0 && b > 0
  ensures m == lcm(a, b) ==> (m % a == 0 && m % b == 0)
{
  var g := gcd(a, b);
  var m_calc := a * (b / g);
  assert m_calc % a == 0 && m_calc % b == 0;
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
  requires a > 0  // Added to handle non-zero case
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  if a > 0 {
    var g := gcd(a, b);
    assert b % g == 0;
    if a < b {
      gcd_division(a, b % a);
    } else {
      gcd_division(b, a % b);
    }
  }
}

lemma gcd_division_zero(a: int, b: int)
  requires a == 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
}

lemma gcd_symmetry(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
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
  
  var min_wb := min(w, b);
  var full_cycle_matches := cycles * min_wb;
  var partial_matches := min(remainder, min_wb - 1);
  
  var total_matches := full_cycle_matches + partial_matches;
  
  assert total_matches >= 0;
  assert t > 0;
  
  if total_matches == 0 {
    numerator := 0;
    denominator := 1;
  } else {
    var g := gcd(total_matches, t);
    assert g > 0 by { gcd_nonzero(total_matches, t); }
    assert total_matches % g == 0 && t % g == 0 by {
      if total_matches == 0 {
        gcd_division_zero(total_matches, t);
      } else {
        gcd_division(total_matches, t);
      }
    }
    numerator := total_matches / g;
    denominator := t / g;
  }
}
// </vc-code>

