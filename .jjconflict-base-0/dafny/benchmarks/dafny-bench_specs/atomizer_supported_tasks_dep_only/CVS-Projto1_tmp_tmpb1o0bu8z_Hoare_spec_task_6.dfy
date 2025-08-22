//ATOM_PLACEHOLDER_Max

//ATOM_PLACEHOLDER_Test

//ATOM_PLACEHOLDER_m1



//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib


//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add


//ATOM_PLACEHOLDER_addImp


// SPEC 


method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
}




