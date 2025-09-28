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
lemma MinProperties(a: int, b: int)
    ensures min(a, b) <= a
    ensures min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
}

lemma MaxTablesProperties(r: int, g: int, b: int)
    requires ValidInput(r, g, b)
    ensures MaxTables(r, g, b) >= 0
{
    assert (r + g + b) / 3 >= 0;
    assert r + g >= 0;
    assert r + b >= 0;
    assert g + b >= 0;
    MinProperties(min(min((r + g + b) / 3, r + g), r + b), g + b);
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
    var sum := r + g + b;
    var avg := sum / 3;
    var rg := r + g;
    var rb := r + b;
    var gb := g + b;
    
    var temp1 := min(avg, rg);
    var temp2 := min(temp1, rb);
    result := min(temp2, gb);
}
// </vc-code>

