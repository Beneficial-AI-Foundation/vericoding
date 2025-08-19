//ATOM


ghost function sum(n: nat): int
{
  if n == 0 then 0 else n + sum(n - 1)
}


//IMPL 

method Sum(n: nat) returns (s: int)
ensures s == sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sum(i)
  {
    i := i + 1;
    s := s + i;
  }
}