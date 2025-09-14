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
    // Direct calculation approach
    var curr := h * (h+1) * (h+2) / 6;
    var next := (h+1) * (h+2) * (h+3) / 6;
    
    // The difference between consecutive values
    // next - curr = (h+1)(h+2)(h+3)/6 - h(h+1)(h+2)/6
    //             = (h+1)(h+2)/6 * [(h+3) - h]
    //             = (h+1)(h+2)/6 * 3
    //             = (h+1)(h+2)/2
    
    // Since h >= 1, we have (h+1) >= 2 and (h+2) >= 3
    // Therefore (h+1)(h+2)/2 >= 2*3/2 = 3 > 0
    assert (h+1) >= 2;
    assert (h+2) >= 3;
    assert (h+1) * (h+2) >= 6;
    assert (h+1) * (h+2) / 2 >= 3;
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

