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
  decreases b
{
  if a == 0 then b
  else if a < b then gcd(b, a)
  else gcd(a % b, b)
}

lemma gcd_properties(a: int, b: int, d: int)
  requires a >= 0 && b > 0 && d > 0
  ensures gcd(a, b) == d ==> (a % d == 0 && b % d == 0)
{
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
{
  a * b / gcd(a, b)
}

lemma lcm_properties(a: int, b: int, m: int)
  requires a > 0 && b > 0
  ensures m == lcm(a, b) ==> (m % a == 0 && m % b == 0)
{
}

function min(a: int, b: int): int
{
  if a <= b then a else b
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
  var partial_matches := min(remainder + 1, min(w, b));
  
  var total_matches := full_cycle_matches + partial_matches - 1;
  
  var g := gcd(total_matches, t);
  numerator := total_matches / g;
  denominator := t / g;
}
// </vc-code>

