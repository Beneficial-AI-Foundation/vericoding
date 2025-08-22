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
    var j := 0;
    while j < a.Length
        invariant 0 <= j <= a.Length
        invariant forall k | 0 <= k < j :: b[k] == sum(a, k)
    {
        if j == 0 {
            b[j] := a[j];
        } else {
            b[j] := b[j-1] + a[j];
        }
        j := j + 1;
    }
}