//IMPL 
method Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  s := 0;
  var i := 0;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant s == i * (i - 1) / 2
  {
    s := s + i;
    i := i + 1;
  }
}