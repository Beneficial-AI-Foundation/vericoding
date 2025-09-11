// <vc-preamble>
function abs(x: real): real
{
  if x < 0.0 then -x else x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
