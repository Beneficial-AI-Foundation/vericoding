//IMPL MedianOfThree
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
  ensures median == a || median == b || median == c
  ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{
  if a <= b && a <= c {
    if b <= c {
      median := b;
    } else {
      median := c;
    }
  } else if b <= a && b <= c {
    if a <= c {
      median := a;
    } else {
      median := c;
    }
  } else {
    if a <= b {
      median := a;
    } else {
      median := b;
    }
  }
}