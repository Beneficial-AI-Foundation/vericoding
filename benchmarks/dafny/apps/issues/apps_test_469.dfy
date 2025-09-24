// <vc-preamble>
predicate ValidInput(r: int, h: int) {
  r >= 1 && h >= 1 && r <= 10000000 && h <= 10000000
}

function ComputeMaxBalloons(r: int, h: int): int
  requires ValidInput(r, h)
{
  var d := h % r;
  if d * 2 < r then
    h / r * 2 + 1
  else if 1732 * r <= 2000 * d + 2000 then
    h / r * 2 + 3
  else
    h / r * 2 + 2
}

predicate ValidOutput(r: int, h: int, result: int) {
  ValidInput(r, h) ==> result >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(r: int, h: int) returns (result: int)
  requires ValidInput(r, h)
  ensures ValidOutput(r, h, result)
  ensures result == ComputeMaxBalloons(r, h)
// </vc-spec>
// <vc-code>
{
  var d := h % r;

  if d * 2 < r {
    result := h / r * 2 + 1;
  } else if 1732 * r <= 2000 * d + 2000 {
    result := h / r * 2 + 3;
  } else {
    result := h / r * 2 + 2;
  }
}
// </vc-code>
