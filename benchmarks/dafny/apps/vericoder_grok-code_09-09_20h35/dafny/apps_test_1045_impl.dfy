predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
lemma TotalCubesIncreasing(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h) < TotalCubesForHeight(h + 1)
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
    var h := 1;
    while TotalCubesForHeight(h + 1) <= n
        invariant h >= 1 && TotalCubesForHeight(h) <= n
        decreases n - TotalCubesForHeight(h)
    {
        h := h + 1;
    }
    assert TotalCubesForHeight(h + 1) > n;
    return h;
}
// </vc-code>

