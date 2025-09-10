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

