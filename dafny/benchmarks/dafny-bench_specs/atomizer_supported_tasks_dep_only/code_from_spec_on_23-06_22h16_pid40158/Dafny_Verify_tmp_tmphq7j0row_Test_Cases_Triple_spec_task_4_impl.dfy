//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_TripleIf

//ATOM_PLACEHOLDER_TripleOver

//IMPL 
method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
    r := 3 * x;
}

//ATOM_PLACEHOLDER_Caller