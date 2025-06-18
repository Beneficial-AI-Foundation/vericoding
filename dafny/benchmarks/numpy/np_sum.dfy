// ATOMS

// HINTS

// RESTRICTIONS

// SPECIFICATION
method Sum(a: array<int>) returns (res: int)
ensures res == SumArray(a, 0, a.Length)
function SumArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
{}