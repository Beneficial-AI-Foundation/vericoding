//ATOM_PLACEHOLDER_Max

//ATOM_PLACEHOLDER_Test

//ATOM_PLACEHOLDER_m1

//ATOM_PLACEHOLDER_fib

//ATOM_PLACEHOLDER_Fib

//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_add

//ATOM_PLACEHOLDER_addImp

//IMPL MaxA
method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
    m := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] <= m
        invariant exists j :: 0 <= j < i && a[j] == m
    {
        if a[i] > m {
            m := a[i];
        }
        i := i + 1;
    }
}