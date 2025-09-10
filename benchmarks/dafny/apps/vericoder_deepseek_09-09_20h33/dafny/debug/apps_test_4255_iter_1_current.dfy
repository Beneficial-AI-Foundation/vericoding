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
lemma TriangleAreaNonNegative(ab: int, bc: int)
    requires ab >= 1 && bc >= 1
    ensures TriangleArea(ab, bc) >= 0
{
}

lemma TriangleAreaWithinBounds(ab: int, bc: int)
    requires ab >= 1 && bc >= 1
    requires ab <= 100 && bc <= 100
    ensures TriangleArea(ab, bc) <= 5000
{
}
// </vc-helpers>

// <vc-spec>
method solve(ab: int, bc: int, ca: int) returns (result: string)
    requires ValidInput(ab, bc, ca)
    ensures exists area :: ValidArea(ab, bc, area) && result == IntToString(area) + "\n"
// </vc-spec>
// <vc-code>
{
    var area := (ab * bc) / 2;
    result := IntToString(area) + "\n";
}
// </vc-code>

