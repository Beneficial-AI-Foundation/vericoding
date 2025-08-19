//ATOM
function calcSum(n: nat) : nat 
{  
  n * (n - 1) / 2
}

//IMPL
method sum(n: nat) returns(s: nat)
  ensures s == calcSum(n + 1)
{
  s := 0;
  var i := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant s == i * (i - 1) / 2
  {
    s := s + i;
    i := i + 1;
  }
}