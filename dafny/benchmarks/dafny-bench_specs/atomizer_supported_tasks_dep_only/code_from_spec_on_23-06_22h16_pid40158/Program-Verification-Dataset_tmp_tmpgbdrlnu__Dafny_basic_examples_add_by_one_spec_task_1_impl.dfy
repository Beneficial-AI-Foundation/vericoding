//IMPL 
method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  r := x;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == x + i
  {
    r := r + 1;
    i := i + 1;
  }
}