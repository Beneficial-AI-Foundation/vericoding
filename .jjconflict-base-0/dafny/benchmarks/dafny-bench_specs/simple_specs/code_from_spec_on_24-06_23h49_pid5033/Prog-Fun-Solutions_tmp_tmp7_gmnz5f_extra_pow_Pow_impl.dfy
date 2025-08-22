//ATOM
ghost function pow(a: int, e: nat): int {
  if e == 0 then 1 else a*pow(a, e-1)
}

//IMPL
method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{
    y := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant y == pow(a, i)
    {
        y := y * a;
        i := i + 1;
    }
}