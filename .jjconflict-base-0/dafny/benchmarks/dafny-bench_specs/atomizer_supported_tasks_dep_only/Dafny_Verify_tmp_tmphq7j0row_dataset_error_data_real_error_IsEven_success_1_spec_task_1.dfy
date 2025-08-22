// ATOM 
function even(n: int): bool
  requires n >= 0
{
  if n == 0 then true else !even(n-1)
}


// SPEC 

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{
}


