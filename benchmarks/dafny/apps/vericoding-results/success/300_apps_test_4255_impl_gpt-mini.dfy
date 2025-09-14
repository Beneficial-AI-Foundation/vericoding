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
function DigitChar(d: int): string
    requires 0 <= d < 10
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
}

function IntToString(x: int): string
    requires x >= 0
    decreases x
{
    if x < 10 then DigitChar(x)
    else IntToString(x / 10) + DigitChar(x % 10)
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
  // Prove the area satisfies the ValidArea predicate
  assert area == TriangleArea(ab, bc);
  assert area >= 0;
  assert ab <= 100 && bc <= 100; // from ValidInput precondition
  assert ab * bc <= 100 * 100;
  assert area <= 5000;
  assert ValidArea(ab, bc, area);
  result := IntToString(area) + "\n";
}
// </vc-code>

