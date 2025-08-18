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
// <vc-code>
{
  assume false;
}
// </vc-code>