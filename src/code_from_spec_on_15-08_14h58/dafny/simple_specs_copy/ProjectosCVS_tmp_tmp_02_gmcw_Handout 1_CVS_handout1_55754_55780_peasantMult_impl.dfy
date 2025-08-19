//IMPL 
method peasantMult(a: int, b: int) returns (r: int)
  requires b > 0
  ensures r == a * b
{
  var x := a;
  var y := b;
  r := 0;
  
  while y > 0
    invariant r + x * y == a * b
    invariant y >= 0
    decreases y
  {
    if y % 2 == 1 {
      r := r + x;
    }
    x := x * 2;
    y := y / 2;
  }
}