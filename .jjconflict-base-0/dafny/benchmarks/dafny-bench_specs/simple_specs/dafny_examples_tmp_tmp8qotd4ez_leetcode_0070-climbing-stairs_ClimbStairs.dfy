//ATOM
function Stairs(n: nat): nat {
 if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}


// SPEC

// A simple specification
method ClimbStairs(n: nat) returns (r: nat)
 ensures r == Stairs(n)
{
}
