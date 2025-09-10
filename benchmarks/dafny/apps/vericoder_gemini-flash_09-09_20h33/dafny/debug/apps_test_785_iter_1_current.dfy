predicate ValidInput(n: int, a: int, b: int)
{
  n > 0 && a > 0 && b > 0
}

predicate ValidOutput(result: seq<int>, n: int, a: int, b: int)
{
  |result| == 3 &&
  result[0] >= 6 * n &&
  result[1] > 0 && result[2] > 0 &&
  result[0] == result[1] * result[2] &&
  ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures var g := gcd(a, b); g > 0 && a % g == 0 && b % g == 0
  ensures forall x :: x > 0 && a % x == 0 && b % x == 0 ==> x <= g
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures var l := lcm(a, b); l > 0 && l % a == 0 && l % b == 0
  ensures forall x :: x > 0 && x % a == 0 && x % b == 0 ==> x >= l
{
  (a / gcd(a, b)) * b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var common_multiple := lcm(a, b);
  var k := (6 * n + common_multiple - 1) / common_multiple;
  var R0 := k * common_multiple;
  var R1 := common_multiple;
  var R2 := 1; 

  if a >= b {
    R1 := a;
    R2 := R0 / a;
  } else {
    R1 := b;
    R2 := R0 / b;
  }

  result := [R0, R1, R2];
}
// </vc-code>

