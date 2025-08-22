//Problem01
//a)
//ATOM_PLACEHOLDER_swap

//b)
//Problem04
//IMPL FindMin

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    minIdx := lo;
    var i := lo + 1;
    
    while i < a.Length
        invariant lo <= minIdx < a.Length
        invariant lo <= i <= a.Length
        invariant forall x :: lo <= x < i ==> a[minIdx] <= a[x]
    {
        if a[i] < a[minIdx] {
            minIdx := i;
        }
        i := i + 1;
    }
}

//Problem02
//ATOM_PLACEHOLDER_sorted

//ATOM_PLACEHOLDER_selectionSort

//Problem03

//Problem03