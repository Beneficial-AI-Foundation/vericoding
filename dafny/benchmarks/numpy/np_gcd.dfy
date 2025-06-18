// ATOMS

// HINTS

// RESTRICTIONS

// SPECIFICATION
method GCD(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> GCDInt(a[i], b[i]) == res[i]
{}