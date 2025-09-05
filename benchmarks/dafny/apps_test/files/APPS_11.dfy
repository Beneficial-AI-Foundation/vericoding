This problem involves painting n tiles (indexed 1 to n) according to specific rules to maximize chocolate rewards. Tiles can be painted Red if divisible by 'a', Blue if divisible by 'b', and for tiles divisible by both, either color can be chosen. The goal is to determine the optimal coloring strategy to maximize total chocolates, where Red tiles give 'p' chocolates and Blue tiles give 'q' chocolates.

The solution uses mathematical insights about divisibility, LCM (Least Common Multiple), and optimal decision-making to determine whether tiles divisible by both 'a' and 'b' should be painted Red or Blue based on which color yields more chocolates.

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

// ======= HELPERS =======
method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b >= 0
  ensures result > 0
  ensures result == gcd_func(a, b)
  ensures (a % result == 0) && (b % result == 0)
{
  var x := a;
  var y := b;
  while y != 0
    invariant x > 0 && y >= 0
    invariant gcd_func(a, b) == gcd_func(x, y)
    decreases y
  {
    var temp := x % y;
    x := y;
    y := temp;
  }
  result := x;
}

// ======= MAIN METHOD =======
method solve(n: int, a: int, b: int, p: int, q: int) returns (maxChocolates: int)
  requires ValidInput(n, a, b, p, q)
  ensures maxChocolates == MaxChocolates(n, a, b, p, q)
{
  var g := gcd(a, b);
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
