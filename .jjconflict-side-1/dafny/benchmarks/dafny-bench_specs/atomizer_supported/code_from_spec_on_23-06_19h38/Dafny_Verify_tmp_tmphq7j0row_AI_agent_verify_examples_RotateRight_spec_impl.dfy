//IMPL 
method RotateRight(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{
    var temp := a[a.Length - 1];
    var i := a.Length - 1;
    
    while i > 0
        invariant 0 <= i < a.Length
        invariant forall j :: i < j < a.Length ==> a[j] == old(a[j-1])
        invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
        invariant temp == old(a[a.Length-1])
    {
        a[i] := a[i-1];
        i := i - 1;
    }
    
    a[0] := temp;
}