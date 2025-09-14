predicate ValidInput(r: int, g: int, b: int) {
    r >= 0 && g >= 0 && b >= 0
}

function MaxTables(r: int, g: int, b: int): int
    requires ValidInput(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

function min(a: int, b: int): int {
    if a <= b then a else b
}

// <vc-helpers>
lemma MaxTablesNonNegative(r: int, g: int, b: int)
    requires ValidInput(r, g, b)
    ensures MaxTables(r, g, b) >= 0
{
    // Since r >= 0, g >= 0, b >= 0, all sums are non-negative
    // and the minimum of non-negative values is non-negative
}
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var sum_all := (r + g + b) / 3;
    var sum_rg := r + g;
    var sum_rb := r + b;
    var sum_gb := g + b;
    
    var min1 := min(sum_all, sum_rg);
    var min2 := min(min1, sum_rb);
    result := min(min2, sum_gb);
    
    MaxTablesNonNegative(r, g, b);
}
// </vc-code>

