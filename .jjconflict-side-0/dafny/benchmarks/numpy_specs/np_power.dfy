//SPEC
method Power(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == Pow(a[i], b[i])
{}