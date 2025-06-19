//SPEC
method Min(a: array<int>) returns (res: int)
requires a.Length > 0
ensures exists i :: 0 <= i < a.Length && res == a[i]
ensures forall i :: 0 <= i < a.Length ==> res <= a[i]
{}