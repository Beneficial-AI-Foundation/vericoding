//ATOM
function Stairs(n: nat): nat {
 if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

//IMPL 
method ClimbStairs(n: nat) returns (r: nat)
 ensures r == Stairs(n)
{
  /* code modified by LLM (iteration 1): removed invalid explanatory text at the beginning of file */
  r := Stairs(n);
}