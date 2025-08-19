//ATOM

ghost function sum(n: nat): int
{
  if n == 0 then 0 else n + sum(n - 1)
}


// SPEC

method Sum(n: nat) returns (s: int)
ensures s == sum(n)
{
}