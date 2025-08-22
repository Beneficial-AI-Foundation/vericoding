//IMPL plus_one
method plus_one (x: int) returns (r:int)
  requires x >= 0;
  ensures r == x + 1;
{
  r := x + 1;
}

//IMPL add_by_one
method add_by_one (x:int, y:int) returns (r:int)
{
  r := x + y;
}