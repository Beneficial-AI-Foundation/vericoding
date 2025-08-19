//IMPL 
method TriangleNumber(N: int) returns (t: int)
  requires N >= 0
  ensures t == N * (N + 1) / 2
{
  t := 0;
  var i := 1;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant t == (i - 1) * i / 2
  {
    t := t + i;
    i := i + 1;
  }
}