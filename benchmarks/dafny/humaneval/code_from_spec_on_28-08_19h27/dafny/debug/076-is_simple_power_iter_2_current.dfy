function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma PowerPositive(x: nat, y: nat)
  requires x > 0
  ensures power(x, y) > 0
{
  if y == 0 {
    // power(x, 0) == 1 > 0
  } else {
    PowerPositive(x, y-1);
    // power(x, y) == x * power(x, y-1) > 0 since x > 0 and power(x, y-1) > 0
  }
}

lemma PowerMonotonic(x: nat, y1: nat, y2: nat)
  requires x > 1 && y1 < y2
  ensures power(x, y1) < power(x, y2)
{
  if y2 == y1 + 1 {
    // power(x, y2) == x * power(x, y1) > power(x, y1) since x > 1
  } else {
    PowerMonotonic(x, y1, y2-1);
    // power(x, y2) == x * power(x, y2-1) > power(x, y1) since x > 1 and power(x, y2-1) > power(x, y1)
  }
}

ghost function is_simple_power_spec(x: int, n: int): bool
  requires x >= 1 && n >= 1
{
  if n == 1 then
    x == 1
  else
    exists k: nat :: power(n, k) == x
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_simple_power(x: int, n: int) -> bool
Your task is to write a function that returns true if a number x is a simple power of n and false in other cases. x is a simple power of n if n**int=x
*/
// </vc-description>

// <vc-spec>
function is_simple_power(x: int, n: int): bool
  requires x >= 1 && n >= 1
  ensures is_simple_power(x, n) == is_simple_power_spec(x, n)
// </vc-spec>
// <vc-code>
{
  if n == 1 then
    x == 1
  else
    var k := 0;
    var pow := 1;
    while pow < x && k < x
      invariant pow == power(n, k)
      invariant pow <= x
      decreases x - pow
    {
      k := k + 1;
      pow := pow * n;
    }
    pow == x
}
// </vc-code>
