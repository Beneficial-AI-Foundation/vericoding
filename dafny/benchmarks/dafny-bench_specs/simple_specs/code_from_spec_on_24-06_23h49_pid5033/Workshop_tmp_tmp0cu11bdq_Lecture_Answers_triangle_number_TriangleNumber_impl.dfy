//IMPL 
method TriangleNumber(N: int) returns (t: int)
  requires N >= 0
  ensures t == N * (N + 1) / 2
{
  t := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant t == i * (i + 1) / 2
  {
    i := i + 1;
    t := t + i;
  }
}