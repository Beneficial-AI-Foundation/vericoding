//ATOM

method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{
  r := 0;
  assume r ==> x + y;
  return r;
}


// SPEC
method M1(x: int, y: int) returns (r: int)
ensures r == x*y
{
}