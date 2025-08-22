//ATOM_PLACEHOLDER_Power

//IMPL CalcPower
method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2 * n;
}

//ATOM_PLACEHOLDER_ComputePower