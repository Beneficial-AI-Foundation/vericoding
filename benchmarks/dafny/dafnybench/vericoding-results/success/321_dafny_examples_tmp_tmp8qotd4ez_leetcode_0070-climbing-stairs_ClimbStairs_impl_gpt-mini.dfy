function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    r := 1;
    return;
  }
  var a := 1; // Stairs(0)
  var b := 1; // Stairs(1)
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
    decreases n - i
  {
    var c := a + b;
    a := b;
    b := c;
    i := i + 1;
  }
  r := b;
}
// </vc-code>

