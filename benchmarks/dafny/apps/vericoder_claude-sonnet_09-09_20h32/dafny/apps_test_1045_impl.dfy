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
    ensures TotalCubesForHeight(h + 1) > TotalCubesForHeight(h)
{
    assert TotalCubesForHeight(h + 1) == (h + 1) * (h + 2) * (h + 3) / 6;
    assert TotalCubesForHeight(h) == h * (h + 1) * (h + 2) / 6;
}

lemma TotalCubesPositive(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h) >= 1
{
}

lemma SearchBounds(n: int, h: int)
    requires ValidInput(n)
    requires h >= 1
    requires TotalCubesForHeight(h) <= n
    requires TotalCubesForHeight(h + 1) > n
    ensures ValidPyramidHeight(n, h)
{
}
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
        invariant h >= 1
        invariant TotalCubesForHeight(h) <= n
        decreases n - TotalCubesForHeight(h)
    {
        TotalCubesIncreasing(h);
        h := h + 1;
    }
    
    SearchBounds(n, h);
    result := h;
}
// </vc-code>

