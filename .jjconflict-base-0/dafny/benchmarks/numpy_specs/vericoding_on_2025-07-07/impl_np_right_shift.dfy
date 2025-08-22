//IMPL
method RightShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] <= 65535
requires forall i :: 0 <= i < b.Length ==> b[i] < 16
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] ==  ((a[i] as bv16) >> (b[i] as nat)) as int
{
    res := new int[a.Length];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == ((a[j] as bv16) >> (b[j] as nat)) as int
    {
        res[i] := ((a[i] as bv16) >> (b[i] as nat)) as int;
        i := i + 1;
    }
}