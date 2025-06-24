// ATOM 
function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// IMPL 
method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{
    b[0] := a[0];
    var j := 1;
    while j < a.Length
        invariant 1 <= j <= a.Length
        invariant forall k | 0 <= k < j :: b[k] == sum(a, k)
    {
        b[j] := a[j] + b[j-1];
        j := j + 1;
    }
}