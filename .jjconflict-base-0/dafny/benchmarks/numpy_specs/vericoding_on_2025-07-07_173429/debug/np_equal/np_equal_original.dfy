//SPEC
method Equal(a: array<int>, b: array<int>) returns (res: array<bool>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] == b[i])
{}