// <vc-preamble>
// Method that computes the Heaviside step function element-wise
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): monotonicity of sign mapping for non-zero reals */
lemma sign_nonneg_monotone(a: real, b: real)
  requires a <= b && a != 0.0 && b != 0.0
  ensures (if a < 0.0 then 0.0 else 1.0) <= (if b < 0.0 then 0.0 else 1.0)
{
  if a < 0.0 {
    if b < 0.0 {
      assert (if a < 0.0 then 0.0 else 1.0) == 0.0;
      assert (if b < 0.0 then 0.0 else 1.0) == 0.0;
    } else {
      // a < 0.0 and b > 0.0
      assert (if a < 0.0 then 0.0 else 1.0) == 0.0;
      assert (if b < 0.0 then 0.0 else 1.0) == 1.0;
    }
  } else {
    // a > 0.0 (since a != 0.0 and not a < 0.0)
    assert (if a < 0.0 then 0.0 else 1.0) == 1.0;
    // from a > 0.0 and a <= b and b != 0.0, we get b > 0.0
    assert b > 0.0;
    assert (if b < 0.0 then 0.0 else 1.0) == 1.0;
  }
  assert (if a < 0.0 then 0.0 else 1.0) <= (if b < 0.0 then 0.0 else 1.0);
}

// </vc-helpers>

// <vc-spec>
method heaviside(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Input vectors must have the same length
  requires |x1| == |x2|
  
  // Output has the same length as inputs
  ensures |result| == |x1|
  
  // Core Heaviside function behavior for each element
  ensures forall i :: 0 <= i < |result| ==>
    (x1[i] < 0.0 ==> result[i] == 0.0) &&
    (x1[i] == 0.0 ==> result[i] == x2[i]) &&
    (x1[i] > 0.0 ==> result[i] == 1.0)
  
  // Each result element is either 0, 1, or the corresponding x2 value
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == 0.0 || result[i] == 1.0 || result[i] == x2[i]
  
  // Monotonicity property: for non-zero x1 values, if x1[i] <= x1[j] then result[i] <= result[j]
  ensures forall i, j :: (0 <= i < |result| && 0 <= j < |result| &&
    x1[i] <= x1[j] && x1[i] != 0.0 && x1[j] != 0.0) ==>
    result[i] <= result[j]
  
  // Boundary behavior: if result is not 0 or 1, then it must be x2
  ensures forall i :: 0 <= i < |result| ==>
    (result[i] != 0.0 && result[i] != 1.0) ==> result[i] == x2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement element-wise Heaviside and prove monotonicity using helper */
{
  var n := |x1|;
  var arr := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==>
      (x1[k] < 0.0 ==> arr[k] == 0.0) &&
      (x1[k] == 0.0 ==> arr[k] == x2[k]) &&
      (x1[k] > 0.0 ==> arr[k] == 1.0)
    invariant forall k :: 0 <= k < i ==> (arr[k] == 0.0 || arr[k] == 1.0 || arr[k] == x2[k])
  {
    if x1[i] < 0.0 {
      arr[i] := 0.0;
    } else if x1[i] == 0.0 {
      arr[i] := x2[i];
    } else {
      arr[i] := 1.0;
    }
    i := i + 1;
  }
  assert i == n;
  result := arr[..];
  assert forall k :: 0 <= k < n ==>
    result[k] == (if x1[k] < 0.0 then 0.0 else if x1[k] == 0.0 then x2[k] else 1.0);

  var ii := 0;
  while ii < n
    invariant 0 <= ii <= n
  {
    var jj := 0;
    while jj < n
      invariant 0 <= jj <= n
    {
      if x1[ii] != 0.0 && x1[jj] != 0.0 && x1[ii] <= x1[jj] {
        if x1[ii] < 0.0 {
          assert result[ii] == 0.0;
        } else {
          // x1[ii] > 0.0
          assert x1[ii] > 0.0;
          assert result[ii] == 1.0;
        }
        if x1[jj] < 0.0 {
          assert result[jj] == 0.0;
        } else {
          // x1[jj] > 0.0
          assert x1[jj] > 0.0;
          assert result[jj] == 1.0;
        }
        sign_nonneg_monotone(x1[ii], x1[jj]);
        assert (if x1[ii] < 0.0 then 0.0 else 1.0) == result[ii];
        assert (if x1[jj] < 0.0 then 0.0 else 1.0) == result[jj];
        assert result[ii] <= result[jj];
      }
      jj := jj + 1;
    }
    ii := ii + 1;
  }
}

// </vc-code>
