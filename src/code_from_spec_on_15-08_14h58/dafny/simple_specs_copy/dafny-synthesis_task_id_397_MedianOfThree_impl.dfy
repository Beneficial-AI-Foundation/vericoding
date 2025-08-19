//IMPL 
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
  ensures median == a || median == b || median == c
  ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{
  if a >= b && a <= c {
    median := a;
  } else if a >= c && a <= b {
    median := a;
  } else if b >= a && b <= c {
    median := b;
  } else if b >= c && b <= a {
    median := b;
  } else if c >= a && c <= b {
    median := c;
  } else {
    median := c;
  }
}