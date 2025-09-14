function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>
// The helpers section can remain empty, as the implementation uses loop invariants directly in the code.
// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 1;
  }
  var i: int := 2;
  var a: nat := 1;
  var b: nat := 1;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i - 2)
  {
    var temp: nat := a + b;
    b := a;
    a := temp;
    i := i + 1;
  }
  assert a == Stairs(n);
  return a;
}
// </vc-code>

