//SPEC
method LeftShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] < 16
requires forall i :: 0 <= i < a.Length ==> a[i] < (1 as bv16)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == ((a[i] as bv16) << (b[i] as bv16)) as int
{}