//ATOM_PLACEHOLDER_UpWhileLess


//ATOM_PLACEHOLDER_UpWhileNotEqual


//ATOM_PLACEHOLDER_DownWhileNotEqual


//IMPL DownWhileGreater
method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i > 0
        invariant 0 <= i
    {
        i := i - 1;
    }
}

//ATOM_PLACEHOLDER_Quotient

//ATOM_PLACEHOLDER_Quotient1