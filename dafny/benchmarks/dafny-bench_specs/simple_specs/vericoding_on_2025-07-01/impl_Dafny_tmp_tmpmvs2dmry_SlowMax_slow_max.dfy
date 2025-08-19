//ATOM

function max(x:nat, y:nat) : nat
{
 if (x < y) then y else x
}


// SPEC

method slow_max(a: nat, b: nat) returns (z: nat)
 ensures z == max(a, b)
{
}