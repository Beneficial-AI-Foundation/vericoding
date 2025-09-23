// <vc-preamble>
predicate ValidBrotherNumbers(a: int, b: int)
{
  1 <= a <= 3 && 1 <= b <= 3 && a != b
}

function LateBrother(a: int, b: int): int
  requires ValidBrotherNumbers(a, b)
{
  6 - a - b
}

predicate IsValidResult(a: int, b: int, result: int)
{
  ValidBrotherNumbers(a, b) ==> 
    (1 <= result <= 3 && result != a && result != b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidBrotherNumbers(a, b)
  ensures IsValidResult(a, b, result)
  ensures result == LateBrother(a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
