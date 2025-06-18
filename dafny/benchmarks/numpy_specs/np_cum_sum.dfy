// ATOMS

// HINTS

// RESTRICTIONS

// SPECIFICATION
method CumSum(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures res.Length > 0 ==> res[0] == a[0]
ensures forall i :: 1 <= i < a.Length ==> res[i] == res[i-1] + a[i]
{}