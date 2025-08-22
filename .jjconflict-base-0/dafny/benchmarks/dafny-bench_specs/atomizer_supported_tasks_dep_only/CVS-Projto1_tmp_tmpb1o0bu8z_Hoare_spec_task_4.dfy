//ATOM_PLACEHOLDER_Max

//ATOM_PLACEHOLDER_Test

//ATOM_PLACEHOLDER_m1



// ATOM 



function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}


// SPEC 

method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{
}



//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add


//ATOM_PLACEHOLDER_addImp


//ATOM_PLACEHOLDER_MaxA



