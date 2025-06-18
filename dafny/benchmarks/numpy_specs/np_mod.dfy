// ATOMS

// HINTS

// RESTRICTIONS

// SPECIFICATION
method Mod(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] != 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] % b[i]
{}