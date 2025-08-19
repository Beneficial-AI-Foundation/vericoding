//ATOM
// Author: Shaobo He

predicate sqrt(x: int, r: int) {
  r*r <= x && (r+1)*(r+1) > x
}

//IMPL mySqrt
method mySqrt(x: int) returns (res: int)
requires 0 <= x
ensures sqrt(x, res)
{
  res := 0;
  while (res + 1) * (res + 1) <= x
    invariant res * res <= x
    invariant res >= 0
  {
    res := res + 1;
  }
}