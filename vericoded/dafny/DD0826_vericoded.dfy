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
  if n == 0 {
    return 1;
  }
  if n == 1 {
    return 1;
  }
  
  var prev2 := 1;
  var prev1 := 1;
  var i := 2;
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant prev2 == Stairs(i - 2)
    invariant prev1 == Stairs(i - 1)
  {
    var temp := prev1 + prev2;
    prev2 := prev1;
    prev1 := temp;
    i := i + 1;
  }
  
  return prev1;
}
// </vc-code>

