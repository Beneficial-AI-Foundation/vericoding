//IMPL 
method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
{
    result := new int[a.Length];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] % b[j]
    {
        result[i] := a[i] % b[i];
        i := i + 1;
    }
}