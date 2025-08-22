//IMPL addArrays
method addArrays(a : array<int>, b : array<int>) returns (c : array<int>) 
requires a.Length == b.Length
ensures b.Length == c.Length
ensures forall i:int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
{
    c := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant c.Length == a.Length
        invariant forall j:int :: 0 <= j < i ==> c[j] == a[j] + b[j]
    {
        c[i] := a[i] + b[i];
        i := i + 1;
    }
}