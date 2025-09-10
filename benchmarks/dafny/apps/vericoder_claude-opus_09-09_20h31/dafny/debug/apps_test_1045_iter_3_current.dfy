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
lemma TotalCubesMonotonic(h1: int, h2: int)
    requires h1 >= 1 && h2 >= h1
    ensures TotalCubesForHeight(h1) <= TotalCubesForHeight(h2)
{
    if h1 == h2 {
        // Base case: equal heights have equal total cubes
    } else {
        // Inductive case: use recursion and transitivity
        TotalCubesMonotonic(h1, h2 - 1);
        TotalCubesGrowth(h2 - 1);
    }
}

lemma TotalCubesForOne()
    ensures TotalCubesForHeight(1) == 1
{
    assert TotalCubesForHeight(1) == 1 * 2 * 3 / 6 == 1;
}

lemma TotalCubesGrowth(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h+1) > TotalCubesForHeight(h)
{
    // Simplified direct proof
    var next := (h+1) * (h+2) * (h+3) / 6;
    var curr := h * (h+1) * (h+2) / 6;
    
    // Show that the numerator difference is positive
    assert (h+1) * (h+2) * (h+3) - h * (h+1) * (h+2) == (h+1) * (h+2) * 3;
    assert (h+1) >= 2;
    assert (h+2) >= 3;
    assert (h+1) * (h+2) >= 6;
    assert (h+1) * (h+2) * 3 >= 18;
    
    // Therefore the difference is at least 3
    assert next - curr == (h+1) * (h+2) * 3 / 6;
    assert next - curr == (h+1) * (h+2) / 2;
    assert next - curr >= 3;
    assert next > curr;
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
    
    TotalCubesForOne();
    assert TotalCubesForHeight(1) == 1;
    
    while TotalCubesForHeight(h + 1) <= n
        invariant h >= 1
        invariant TotalCubesForHeight(h) <= n
        decreases n - TotalCubesForHeight(h)
    {
        TotalCubesGrowth(h);
        h := h + 1;
    }
    
    assert TotalCubesForHeight(h) <= n;
    assert TotalCubesForHeight(h + 1) > n;
    
    result := h;
}
// </vc-code>

