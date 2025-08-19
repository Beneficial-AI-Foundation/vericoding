//IMPL 
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
    index := from;
    var i := from + 1;
    
    while i < to
        invariant from <= index < to
        invariant from + 1 <= i <= to
        invariant forall k :: from <= k < i ==> a[k] >= a[index]
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}