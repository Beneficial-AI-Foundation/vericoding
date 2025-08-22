//ATOM
function abs(x: int): int
{
  if x < 0 then -x else x
}


// SPEC


// Exercise 6:

method Abs(x: int) returns (y: int)
  ensures abs(x) == y
{
}
