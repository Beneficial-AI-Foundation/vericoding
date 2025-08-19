//IMPL 
method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{
    c := new int[a.Length + b.Length];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] == c[j]
    {
        c[i] := a[i];
        i := i + 1;
    }
    
    i := 0;
    while i < b.Length
        invariant 0 <= i <= b.Length
        invariant forall j :: 0 <= j < a.Length ==> a[j] == c[j]
        invariant forall j :: 0 <= j < i ==> b[j] == c[a.Length + j]
    {
        c[a.Length + i] := b[i];
        i := i + 1;
    }
}