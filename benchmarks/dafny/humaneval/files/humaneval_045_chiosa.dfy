// <vc-preamble>
// ======= TASK =======
// Calculate the area of a triangle given the length of its base and height.
// Formula: Area = (base × height) ÷ 2

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(base: real, height: real)
{
    base >= 0.0 && height >= 0.0
}

function TriangleAreaFormula(base: real, height: real): real
{
    (base * height) / 2.0
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
function triangle_area(a: real, h: real): real
    requires a >= 0.0
    requires h >= 0.0
    ensures triangle_area(a, h) >= 0.0
    ensures triangle_area(a, h) == (a * h) / 2.0
    ensures (a == 0.0 || h == 0.0) ==> triangle_area(a, h) == 0.0
{
    (a * h) / 2.0
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method CalculateTriangleArea(base: real, height: real) returns (area: real)
    requires ValidInput(base, height)
    ensures area >= 0.0
    ensures area == TriangleAreaFormula(base, height)
    ensures (base == 0.0 || height == 0.0) ==> area == 0.0
// </vc-spec>
// <vc-code>
{
    area := triangle_area(base, height);
}
// </vc-code>
