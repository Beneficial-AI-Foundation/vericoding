//IMPL 
method MyMethod(x: int) returns (y: int)
  requires 10 <= x
  ensures 25 <= y
{
  y := x + 15;
}