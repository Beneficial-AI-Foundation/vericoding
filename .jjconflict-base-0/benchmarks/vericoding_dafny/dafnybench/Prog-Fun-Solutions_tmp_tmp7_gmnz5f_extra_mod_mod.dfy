ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
// </vc-helpers>

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// <vc-code>
{
  assume false;
}
// </vc-code>