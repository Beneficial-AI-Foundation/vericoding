//ATOM
function calcSum(n: nat) : nat 
{  
  n * (n - 1) / 2
}

//IMPL sum
method sum(n: nat) returns(s: nat)
  ensures s == calcSum(n + 1)
{
  s := (n + 1) * n / 2;
}