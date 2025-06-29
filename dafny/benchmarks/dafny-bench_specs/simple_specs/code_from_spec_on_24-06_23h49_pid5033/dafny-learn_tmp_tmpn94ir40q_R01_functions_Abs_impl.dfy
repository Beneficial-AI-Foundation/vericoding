//ATOM
function abs(x: int): int
{
  if x < 0 then -x else x
}

//IMPL
method Abs(x: int) returns (y: int)
  ensures abs(x) == y
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}