// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define bounds and prove simple properties about them */
function LowerBound(): real {
  0.707106781186547524400844362104849038
}

/* helper modified by LLM (iteration 3): define bounds and prove simple properties about them */
function UpperBound(): real {
  0.707106781186547524400844362104849040
}

/* helper modified by LLM (iteration 3): show bounds are positive and ordered; also that they tightly bracket sqrt(1/2) */
lemma BoundsEncloseSqrtHalf()
  ensures LowerBound() > 0.0
  ensures LowerBound() <= UpperBound()
  ensures LowerBound()*LowerBound() < 0.5
  ensures UpperBound()*UpperBound() > 0.5
{}

// </vc-helpers>

// <vc-spec>
method NPY_SQRT1_2() returns (result: real)
    // The result is the square root of 1/2, so its square equals 0.5
    ensures result * result == 0.5
    // The result is positive
    ensures result > 0.0
    // The result equals 1 divided by the square root of 2
    ensures result * result * 2.0 == 1.0
    // The result is approximately the known mathematical value
    ensures result >= 0.707106781186547524400844362104849038
    ensures result <= 0.707106781186547524400844362104849040
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): choose the unique positive square root of 1/2 within tight numeric bounds */
  BoundsEncloseSqrtHalf();
  var r: real :| r*r == 0.5 && r > 0.0 && LowerBound() <= r && r <= UpperBound();
  result := r;
}
// </vc-code>
