// ATOMS

// HINTS

// RESTRICTIONS

// SPECIFICATION
method Abs(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == AbsInt(a[i])
ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0
{}