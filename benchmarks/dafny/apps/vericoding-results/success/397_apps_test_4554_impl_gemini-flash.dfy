// <vc-preamble>
predicate ValidInput(W: int, a: int, b: int)
{
    W >= 1 && a >= 1 && b >= 1
}

function AbsDiff(x: int, y: int): int
{
    if x >= y then x - y else y - x
}

function MinMoveDistance(W: int, a: int, b: int): int
    requires ValidInput(W, a, b)
{
    var distance := AbsDiff(a, b);
    if distance <= W then 0
    else distance - W
}

predicate RectanglesConnect(W: int, a: int, b: int)
    requires ValidInput(W, a, b)
{
    AbsDiff(a, b) <= W
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed, providing an empty string */
// </vc-helpers>

// <vc-spec>
method solve(W: int, a: int, b: int) returns (result: int)
    requires ValidInput(W, a, b)
    ensures result == MinMoveDistance(W, a, b)
    ensures result >= 0
    ensures RectanglesConnect(W, a, b) <==> result == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented logic to calculate minimum move distance */
{
  var distance := AbsDiff(a, b);
  if distance <= W {
    result := 0;
  } else {
    result := distance - W;
  }
}
// </vc-code>
