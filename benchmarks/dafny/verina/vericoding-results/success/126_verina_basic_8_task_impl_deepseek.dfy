// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function min(a: int, b: int): int {
  if a < b then a else b
}
lemma MinProperties(a: int, b: int)
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
}

// </vc-helpers>

// <vc-spec>
method MyMin(a: int, b: int) returns (result: int)
    ensures result <= a && result <= b
    ensures result == a || result == b
// </vc-spec>
// <vc-code>
{
  MinProperties(a, b);
  result := min(a, b);
}
// </vc-code>
