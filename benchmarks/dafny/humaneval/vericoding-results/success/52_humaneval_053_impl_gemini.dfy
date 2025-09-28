// <vc-preamble>

predicate ValidInput(x: int, y: int)
{
    true
}

function CorrectSum(x: int, y: int): int
{
    x + y
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures result == CorrectSum(x, y)
// </vc-spec>
// <vc-code>
{
  result := x + y;
}
// </vc-code>
