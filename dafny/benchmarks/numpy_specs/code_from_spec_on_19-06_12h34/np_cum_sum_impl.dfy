//IMPL
method CumSum(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures res.Length > 0 ==> res[0] == a[0]
ensures forall i :: 1 <= i < a.Length ==> res[i] == res[i-1] + a[i]
{
    res := new int[a.Length];
    if a.Length > 0 {
        res[0] := a[0];
        var i := 1;
        while i < a.Length
            invariant 1 <= i <= a.Length
            invariant res[0] == a[0]
            invariant forall j :: 1 <= j < i ==> res[j] == res[j-1] + a[j]
        {
            res[i] := res[i-1] + a[i];
            i := i + 1;
        }
    }
}