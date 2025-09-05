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
method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures (a % result == 0) && (b % result == 0)
{
  var x := a;
  var y := b;
  while y != 0
    invariant x > 0 && y >= 0
    invariant gcd_func(x, y) == gcd_func(a, b)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

lemma lcm_property(a: int, b: int, g: int)
  requires a > 0 && b > 0 && g > 0
  requires (a % g == 0) && (b % g == 0)
  ensures (a * b) / g > 0
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
  lcm_property(a, b, g);
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

