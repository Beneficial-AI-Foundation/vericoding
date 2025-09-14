function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    r := 1;
  } else {
    var a := 1;
    var b := 1;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == Stairs(i - 2)
      invariant b == Stairs(i - 1)
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    r := b;
  }
}
// </vc-code>

