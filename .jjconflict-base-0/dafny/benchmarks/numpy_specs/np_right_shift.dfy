//SPEC
method RightShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] <= 65535
requires forall i :: 0 <= i < b.Length ==> b[i] < 16
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] ==  ((a[i] as bv16) >> (b[i] as nat)) as int
{}