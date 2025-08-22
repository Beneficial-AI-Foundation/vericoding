//IMPL Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
}


//b)
//Problem04
//ATOM_PLACEHOLDER_FindMin

//Problem02
//ATOM_PLACEHOLDER_sorted

//ATOM_PLACEHOLDER_selectionSort


//Problem03






//Problem03