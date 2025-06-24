//Problem01
//a)
//ATOM_PLACEHOLDER_swap

//b)
//Problem04
// SPEC 

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
}


//Problem02
//ATOM_PLACEHOLDER_sorted

//ATOM_PLACEHOLDER_selectionSort


//Problem03






//Problem03



