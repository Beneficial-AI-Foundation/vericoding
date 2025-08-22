//SPEC
method Abs(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == (if a[i] < 0 then -a[i] else a[i])
ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0
{}