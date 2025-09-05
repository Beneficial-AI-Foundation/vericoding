// ======= TASK =======
// Given n tiles indexed 1 to n, paint them according to these rules:
// - A tile can be painted Red if its index is divisible by a
// - A tile can be painted Blue if its index is divisible by b  
// - If a tile's index is divisible by both a and b, choose either Red or Blue (not both)
// - Red tiles give p chocolates each, Blue tiles give q chocolates each
// Find the maximum total chocolates possible.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int, a: int, b: int, p: int, q: int)
{
  n >= 1 && a >= 1 && b >= 1 && p >= 1 && q >= 1
}

function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd_func(a, b) > 0
  ensures (a % gcd_func(a, b) == 0) && (b % gcd_func(a, b) == 0)
  decreases b
{
  if b == 0 then a else gcd_func(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  (a * b) / gcd_func(a, b)
}

function MaxChocolates(n: int, a: int, b: int, p: int, q: int): int
  requires ValidInput(n, a, b, p, q)
{
  var redTiles := n / a;
  var blueTiles := n / b;
  var bothTiles := n / lcm(a, b);
  
  if p >= q then
    redTiles * p + (blueTiles - bothTiles) * q
  else
    blueTiles * q + (redTiles - bothTiles) * p
}

// <vc-helpers>
function gcd_simple(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd_simple(a, b) > 0
  ensures (a % gcd_simple(a, b) == 0) && (b % gcd_simple(a, b) == 0)
  decreases if a > b then a else b
{
  if a == b then a
  else if a > b then gcd_simple(a - b, b)
  else gcd_simple(a, b - a)
}

lemma gcd_equivalence(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd_simple(a, b) == gcd_func(a, b)
{
  if a == b {
    assert gcd_func(a, 0) == a;
  } else if a > b {
    gcd_equivalence(a - b, b);
  } else {
    gcd_equivalence(a, b - a);
  }
}

method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures (a % result == 0) && (b % result == 0)
  ensures result == gcd_func(a, b)
{
  var x := a;
  var y := b;
  while x != y
    invariant x > 0 && y > 0
    invariant gcd_simple(x, y) == gcd_simple(a, b)
    decreases x + y
  {
    if x > y {
      x := x - y;
    } else {
      y := y - x;
    }
  }
  result := x;
  gcd_equivalence(a, b);
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a % gcd_simple(a, b) == 0) && (b % gcd_simple(a, b) == 0)
{
}

lemma lcm_equivalence(a: int, b: int, g: int)
  requires a > 0 && b > 0 && g > 0
  requires (a % g == 0) && (b % g == 0)
  requires g == gcd_func(a, b)
  ensures (a * b) / g == lcm(a, b)
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(n: int, a: int, b: int, p: int, q: int) returns (maxChocolates: int)
  requires ValidInput(n, a, b, p, q)
  ensures maxChocolates == MaxChocolates(n, a, b, p, q)
// </vc-spec>
// <vc-code>
{
  var g := gcd(a, b);
  lcm_equivalence(a, b, g);
  var lcm_ab := (a * b) / g;
  
  var redTiles := n / a;
  var blueTiles := n / b;
  var bothTiles := n / lcm_ab;
  
  if p >= q {
    maxChocolates := redTiles * p + (blueTiles - bothTiles) * q;
  } else {
    maxChocolates := blueTiles * q + (redTiles - bothTiles) * p;
  }
}
// </vc-code>

