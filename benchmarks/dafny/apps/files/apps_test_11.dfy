Given n tiles numbered 1 to n, paint tiles according to rules:
- Tile can be painted Red if divisible by a (gives p chocolates)
- Tile can be painted Blue if divisible by b (gives q chocolates)  
- If divisible by both a and b, choose the color giving more chocolates
Find the maximum total chocolates possible.

predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

method gcd_method(a: int, b: int) returns (result: int)
  requires a > 0 && b >= 0
  ensures result > 0
  ensures result == gcd(a, b)
{
  var x := a;
  var y := b;
  while y != 0
    invariant x > 0 && y >= 0
    invariant gcd(x, y) == gcd(a, b)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
{
  var g := gcd_method(a, b);
  assert g > 0;
  var lcm_ab := (a * b) / g;
  var tiles_a := n / a;
  var tiles_b := n / b;
  var tiles_both := n / lcm_ab;

  result := tiles_a * p + tiles_b * q - tiles_both * (if p < q then p else q);
}
