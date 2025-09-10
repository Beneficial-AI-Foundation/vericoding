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

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
}

function NatToString(n: nat): string
    requires n >= 0
    decreases n
{
    if n < 10 then [digit(n)]
    else NatToString(n / 10) + [digit(n % 10)]
}

function digit(n: nat): char
    requires n < 10
{
    ['0','1','2','3','4','5','6','7','8','9'][n]
}
// </vc-helpers>
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

