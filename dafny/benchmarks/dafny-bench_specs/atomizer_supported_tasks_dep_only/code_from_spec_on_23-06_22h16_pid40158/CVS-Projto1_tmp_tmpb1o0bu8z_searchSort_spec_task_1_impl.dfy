//IMPL 
method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
    modifies a
{
    var i := 0;
    while i < c
        invariant 0 <= i <= c
        invariant forall j :: 0 <= j < i ==> a[j] == k
    {
        a[i] := k;
        i := i + 1;
    }
    b := true;
}