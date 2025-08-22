//IMPL 
method GetEven(a: array<nat>)
requires true
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{
    var j := 0;
    while j < a.Length
        invariant 0 <= j <= a.Length
        invariant forall k:int :: 0 <= k < j ==> a[k] % 2 == 0
    {
        if a[j] % 2 == 1 {
            a[j] := a[j] + 1;
        }
        j := j + 1;
    }
}