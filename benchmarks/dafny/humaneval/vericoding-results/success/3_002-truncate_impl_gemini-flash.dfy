// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix function body type mismatch by ensuring Floor function returns `real` by converting x.Floor to real after computation*/
function Floor(x: real): real {
  if x < 0.0 then (x-1.0).Floor as real else x.Floor as real
}
// </vc-helpers>

// <vc-spec>
method truncate(x : real) returns (i : real)

    requires x >= 0.0

    ensures (0.0 <= x - i < 1.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected the assignment of 'i' with the Floor function to ensure the correct type handling of 'real'. */
{
  i := Floor(x);
}
// </vc-code>
