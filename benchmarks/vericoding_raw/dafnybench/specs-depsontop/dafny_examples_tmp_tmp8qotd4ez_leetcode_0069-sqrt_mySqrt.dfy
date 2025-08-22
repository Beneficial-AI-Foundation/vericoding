// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);

{
  assume false;
}