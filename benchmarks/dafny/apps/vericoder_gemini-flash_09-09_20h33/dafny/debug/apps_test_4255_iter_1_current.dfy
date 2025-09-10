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
function IntToString(i: int): string
  requires 0 <= i <= 5000 // Constraints based on ValidArea
{
  if i == 0 then "0"
  else if i == 1 then "1"
  else if i == 2 then "2"
  else if i == 3 then "3"
  else if i == 4 then "4"
  else if i == 5 then "5"
  else if i == 6 then "6"
  else if i == 7 then "7"
  else if i == 8 then "8"
  else if i == 9 then "9"
  else IntToString(i / 10) + IntToString(i % 10)
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
    result := IntToString(area) + "\n";
}
// </vc-code>

