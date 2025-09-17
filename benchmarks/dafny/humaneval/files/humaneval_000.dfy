// <vc-preamble>

predicate ValidInput(numbers: seq<real>, threshold: real)
{
    true
}

function AbsDiff(a: real, b: real): real
{
    if a >= b then a - b else b - a
}

predicate HasCloseElements(numbers: seq<real>, threshold: real)
{
    exists i, j :: 0 <= i < j < |numbers| && AbsDiff(numbers[i], numbers[j]) < threshold
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    requires ValidInput(numbers, threshold)
    ensures result == HasCloseElements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
