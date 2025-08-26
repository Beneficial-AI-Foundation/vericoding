function Potencia(x: nat, y: nat): nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1) 
}

// <vc-helpers>
// </vc-helpers>

method Pot(x: nat, y: nat) returns (r: nat)
ensures r == Potencia(x,y)
// </vc-spec>
// <vc-code>
{
  r := 1;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant r == Potencia(x, i)
  {
    r := r * x;
    i := i + 1;
  }
}
// </vc-code>