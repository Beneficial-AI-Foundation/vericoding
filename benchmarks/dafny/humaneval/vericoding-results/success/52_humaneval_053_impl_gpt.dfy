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
lemma SumDefinition(x: int, y: int)
  ensures CorrectSum(x, y) == x + y
{
}

// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures result == CorrectSum(x, y)
// </vc-spec>
// <vc-code>
{
  result := CorrectSum(x, y);
}
// </vc-code>
