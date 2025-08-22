//ATOM
function Fat(n:nat):nat
{
  if n == 0 then 1 else n*Fat(n-1)
}

//IMPL 
method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
  f := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant f == Fat(i)
  {
    i := i + 1;
    f := f * i;
  }
}