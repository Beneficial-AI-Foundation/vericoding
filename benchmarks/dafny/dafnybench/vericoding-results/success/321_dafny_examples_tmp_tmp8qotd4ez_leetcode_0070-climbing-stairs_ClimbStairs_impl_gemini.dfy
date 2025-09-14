// <vc-preamble>
function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}
// </vc-preamble>

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
    var prev := 1;
    var curr := 1;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant prev == Stairs(i-1)
      invariant curr == Stairs(i)
    {
      var next := prev + curr;
      prev := curr;
      curr := next;
      i := i + 1;
    }
    r := curr;
  }
}
// </vc-code>
