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
function findHeight(n: int, currentHeight: int): int
    requires n >= 1
    requires currentHeight >= 1
    // A good upper bound for `n` is `currentHeight` in our case, which is guaranteed to be positive.
    // However, `n - TotalCubesForHeight(currentHeight)` can become negative for large currentHeight
    // as it passes n; we use `n` as the termination metric because `h` grows indefinitely such
    // that TotalCubesForHeight(h) could overflow
    decreases n
    ensures ValidPyramidHeight(n, findHeight(n, currentHeight))
{
    if TotalCubesForHeight(currentHeight + 1) > n then
        currentHeight
    else
        findHeight(n, currentHeight + 1)
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
        // Loop terminates as h increases, TotalCubesForHeight(h) increases as well.
        // n is a constant which limits how large TotalCubesForHeight(h) can be.
        decreases n - TotalCubesForHeight(h)
    {
        h := h + 1;
    }
    return h;
}
// </vc-code>

