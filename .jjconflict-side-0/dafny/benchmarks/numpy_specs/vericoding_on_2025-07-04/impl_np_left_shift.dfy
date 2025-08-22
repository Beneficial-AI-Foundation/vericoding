//IMPL
method LeftShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] < 16
/* code modified by LLM (iteration 1): Fixed precondition to use proper bv16 bounds and comparison */
requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < 65536
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == ((a[i] as bv16) << (b[i] as bv16)) as int
{
    res := new int[a.Length];
    var k := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall i :: 0 <= i < k ==> res[i] == ((a[i] as bv16) << (b[i] as bv16)) as int
    {
        res[k] := ((a[k] as bv16) << (b[k] as bv16)) as int;
        k := k + 1;
    }
}