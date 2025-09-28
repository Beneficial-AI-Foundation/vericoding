// <vc-preamble>
// Method to multiply a Laguerre series by x
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [removed unnecessary precondition] */
function LagMulX_Term(i: int, c: seq<real>): real
  requires |c| >= 1
{
    if i-1 < |c| && i-2 >= 0 then
      (-(i as real) * (if i < |c| then c[i] else 0.0) +
      (2.0 * ((i-1) as real) + 1.0) * c[i-1] -
      (i-1) as real * (if i-2 < |c| then c[i-2] else 0.0))
    else
      0.0
}
// </vc-helpers>

// <vc-spec>
method LagMulX(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 1  // Input must be non-empty
  ensures |result| == |c| + 1  // Output has one more coefficient
  ensures |c| >= 1 ==> result[0] == c[0]  // First coefficient preserved
  ensures |c| >= 1 ==> result[1] == -c[0]  // Second coefficient is negative of first input coefficient
  // The recursion relationship for Laguerre polynomials:
  // xP_i(x) = (-(i + 1)*P_{i + 1}(x) + (2i + 1)P_{i}(x) - iP_{i - 1}(x))
  ensures forall i :: 2 <= i < |result| ==> 
    result[i] == if i-1 < |c| && i-2 >= 0 then
      (-(i as real) * (if i < |c| then c[i] else 0.0) + 
       (2.0*((i-1) as real) + 1.0) * c[i-1] - 
       (i-1) as real * (if i-2 < |c| then c[i-2] else 0.0))
    else 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [no change; fix is in the helper function] */
  result := seq(|c| + 1, i =>
    if i == 0 then
      c[0]
    else if i == 1 then
      -c[0]
    else
      LagMulX_Term(i, c)
  );
}
// </vc-code>
