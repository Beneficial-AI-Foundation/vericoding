predicate ValidInput(ab: int, bc: int, ca: int)
{
    1 <= ab <= 100 && 1 <= bc <= 100 && 1 <= ca <= 100
}

function TriangleArea(ab: int, bc: int): int
    requires ab >= 1 && bc >= 1
{
    (ab * bc) / 2
}

predicate ValidArea(ab: int, bc: int, area: int)
    requires ab >= 1 && bc >= 1
{
    area == TriangleArea(ab, bc) && area >= 0 && area <= 5000
}

// <vc-helpers>
function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + IntToString(n % 10)
}

lemma TriangleAreaBounds(ab: int, bc: int)
    requires 1 <= ab <= 100 && 1 <= bc <= 100
    ensures TriangleArea(ab, bc) <= 5000
{
    assert TriangleArea(ab, bc) == (ab * bc) / 2;
    assert ab * bc <= 100 * 100;
    assert (ab * bc) / 2 <= 10000 / 2;
    assert (ab * bc) / 2 <= 5000;
}

lemma TriangleAreaNonNegative(ab: int, bc: int)
    requires ab >= 1 && bc >= 1
    ensures TriangleArea(ab, bc) >= 0
{
    assert ab >= 1 && bc >= 1;
    assert ab * bc >= 1;
    assert (ab * bc) / 2 >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(ab: int, bc: int, ca: int) returns (result: string)
    requires ValidInput(ab, bc, ca)
    ensures exists area :: ValidArea(ab, bc, area) && result == IntToString(area) + "\n"
// </vc-spec>
// <vc-code>
{
    var area := TriangleArea(ab, bc);
    TriangleAreaBounds(ab, bc);
    TriangleAreaNonNegative(ab, bc);
    result := IntToString(area) + "\n";
}
// </vc-code>

