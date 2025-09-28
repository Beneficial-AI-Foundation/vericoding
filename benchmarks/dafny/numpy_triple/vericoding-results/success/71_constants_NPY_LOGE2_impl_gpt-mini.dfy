// <vc-preamble>
// Mathematical constant method that returns the natural logarithm of 2
// </vc-preamble>

// <vc-helpers>
function LogE2Const(): real { 6931474.0 / 10000000.0 }

lemma LogE2ConstBounds()
  ensures 0.693147 < LogE2Const() && LogE2Const() < 0.693148
  ensures 1.386294 < 2.0 * LogE2Const() && 2.0 * LogE2Const() < 1.386295
{
  var r := LogE2Const();
  // Scale by 10^7 to work with integers and make comparisons obvious
  assert r * 10000000.0 == 6931474.0;
  assert 0.693147 * 10000000.0 == 6931470.0;
  assert 0.693148 * 10000000.0 == 6931480.0;
  assert 6931470.0 < 6931474.0;
  assert 6931474.0 < 6931480.0;
  assert 0.693147 * 10000000.0 < r * 10000000.0;
  assert r * 10000000.0 < 0.693148 * 10000000.0;
  // Divide (by a positive number) to obtain the original bounds
  assert 0.693147 < r && r < 0.693148;

  // Now prove the doubled bounds
  assert 2.0 * r * 10000000.0 == 13862948.0;
  assert 1.386294 * 10000000.0 == 13862940.0;
  assert 1.386295 * 10000000.0 == 13862950.0;
  assert 13862940.0 < 13862948.0;
  assert 13862948.0 < 13862950.0;
  assert 1.386294 < 2.0 * r && 2.0 * r < 1.386295;
}

// </vc-helpers>

// <vc-spec>
method NPY_LOGE2() returns (result: real)
  // The value is positive (since 2 > 1 and ln is increasing)
  ensures result > 0.0
  // The value is less than 1 (since 2 < e ≈ 2.718 and ln is increasing)  
  ensures result < 1.0
  // More precise bounds check for ln(2)
  ensures 0.693147 < result && result < 0.693148
  // Mathematical property: 2 * result represents ln(4) with reasonable bounds
  ensures 1.386294 < 2.0 * result && 2.0 * result < 1.386295
// </vc-spec>
// <vc-code>
{
  var r := LogE2Const();
  LogE2ConstBounds();
  result := r;
}

// </vc-code>
