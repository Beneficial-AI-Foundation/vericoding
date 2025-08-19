//ATOM

ghost function f2(n: nat): nat {
  if n == 0 then 0
  else 5*f2(n/3) + n%4
}


// SPEC

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{
}