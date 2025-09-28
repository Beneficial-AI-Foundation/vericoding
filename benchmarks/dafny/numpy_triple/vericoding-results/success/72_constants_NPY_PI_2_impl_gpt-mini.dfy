// <vc-preamble>
// Method that returns the mathematical constant π/2
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define constant for π/2 */
function PiOver2Const(): real {
  15707963.0 / 10000000.0
}

/* helper modified by LLM (iteration 2): prove bounds for the constant */
lemma PiOver2_Bounds()
  ensures 1.5707 < PiOver2Const() < 1.5708
  ensures 1.0 < PiOver2Const() < 2.0
  ensures 2.467 < PiOver2Const() * PiOver2Const() < 2.468
  ensures 3.141 < 2.0 * PiOver2Const() < 3.142
  ensures 0.785 < PiOver2Const() / 2.0 < 0.786
  ensures 4.712 < 3.0 * PiOver2Const() < 4.713
  ensures 6.283 < 4.0 * PiOver2Const() < 6.284
{
  assert 1.5707 < PiOver2Const() && PiOver2Const() < 1.5708;
  assert 1.0 < PiOver2Const() && PiOver2Const() < 2.0;
  assert 2.467 < PiOver2Const() * PiOver2Const() && PiOver2Const() * PiOver2Const() < 2.468;
  assert 3.141 < 2.0 * PiOver2Const() && 2.0 * PiOver2Const() < 3.142;
  assert 0.785 < PiOver2Const() / 2.0 && PiOver2Const() / 2.0 < 0.786;
  assert 4.712 < 3.0 * PiOver2Const() && 3.0 * PiOver2Const() < 4.713;
  assert 6.283 < 4.0 * PiOver2Const() && 4.0 * PiOver2Const() < 6.284;
}

// </vc-helpers>

// <vc-spec>
method NPY_PI_2() returns (result: real)
  // No preconditions needed for a mathematical constant
  ensures 1.5707 < result < 1.5708  // π/2 is approximately 1.5708...
  ensures 1.0 < result < 2.0        // Basic sanity check: π/2 is between 1 and 2
  ensures 2.467 < result * result < 2.468  // π/2 squared is approximately 2.4674...
  ensures 3.141 < 2.0 * result < 3.142     // 2*(π/2) should be approximately π
  ensures 0.785 < result / 2.0 < 0.786     // (π/2)/2 = π/4 is approximately 0.7854...
  ensures 4.712 < 3.0 * result < 4.713     // 3*(π/2) = 3π/2 is approximately 4.7124...
  ensures 6.283 < 4.0 * result < 6.284     // 4*(π/2) = 2π is approximately 6.2832...
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): return constant and invoke bounds lemma */
  result := PiOver2Const();
  PiOver2_Bounds();
}

// </vc-code>
