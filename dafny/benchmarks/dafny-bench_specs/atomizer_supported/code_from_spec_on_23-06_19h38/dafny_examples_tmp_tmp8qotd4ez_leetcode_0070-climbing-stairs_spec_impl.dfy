// ATOM 
function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

//IMPL 
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  if n <= 1 {
    r := 1;
  } else {
    var prev2 := 1;  // Stairs(0)
    var prev1 := 1;  // Stairs(1)
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev2 == Stairs(i - 2)
      invariant prev1 == Stairs(i - 1)
    {
      var current := prev2 + prev1;
      prev2 := prev1;
      prev1 := current;
      i := i + 1;
    }
    
    r := prev1;
  }
}