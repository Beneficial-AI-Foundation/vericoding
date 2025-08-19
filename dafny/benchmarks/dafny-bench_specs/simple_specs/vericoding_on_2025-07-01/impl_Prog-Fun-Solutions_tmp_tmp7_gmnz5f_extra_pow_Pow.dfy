//ATOM

ghost function pow(a: int, e: nat): int {
  if e == 0 then 1 else a*pow(a, e-1)
}


// SPEC

method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{
}