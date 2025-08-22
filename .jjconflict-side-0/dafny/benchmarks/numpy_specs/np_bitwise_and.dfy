//SPEC
method BitwiseAnd(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] <= 65535 &&  0 <= b[i] <= 65535
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] as bv16 & b[i] as bv16) as int
{}