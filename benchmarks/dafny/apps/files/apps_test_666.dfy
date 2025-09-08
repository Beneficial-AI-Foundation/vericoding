Find the n-th element (1-indexed) in an infinite sequence constructed as blocks:
Block 1: [1], Block 2: [1,2], Block 3: [1,2,3], etc.
The complete sequence is: 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3, 4, 5, ...

function TriangularNumber(m: int): int
    requires m >= 0
{
    m * (m + 1) / 2
}

predicate ValidInput(n: int)
{
    n >= 1
}

predicate ValidResult(n: int, result: int)
    requires ValidInput(n)
{
    result >= 1 && result <= n
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
{
    var l: int := 0;
    var r: int := n;

    while r - l > 1 
        invariant 0 <= l < r <= n
        invariant TriangularNumber(l) < n
        invariant TriangularNumber(r) >= n
        decreases r - l
    {
        var m: int := (r + l) / 2;
        if TriangularNumber(m) >= n {
            r := m;
        } else {
            l := m;
        }
    }

    result := n - TriangularNumber(l);
}
