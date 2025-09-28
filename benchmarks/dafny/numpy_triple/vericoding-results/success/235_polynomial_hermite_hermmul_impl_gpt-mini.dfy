// <vc-preamble>
// Method to multiply two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute partial convolution sum up to i */
function sum_prefix(c1: seq<real>, c2: seq<real>, p: int, i: int): real
  requires 0 <= i <= |c1|
  requires 0 <= p < |c1| + |c2| - 1
  decreases i
{
  if i == 0 then 0.0 else
    var x := i - 1;
    var contrib := if 0 <= p - x < |c2| then c1[x] * c2[p - x] else 0.0;
    sum_prefix(c1, c2, p, i - 1) + contrib
}
// </vc-helpers>

// <vc-spec>
method hermmul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  ensures
    // Empty input handling: if either input is empty, return single zero coefficient
    (|c1| == 0 || |c2| == 0) ==> (|result| == 1 && result[0] == 0.0)
  ensures
    // Non-empty inputs have correct output size: m + n - 1 coefficients
    (|c1| > 0 && |c2| > 0) ==> |result| == |c1| + |c2| - 1
  ensures
    // Multiplication by constant polynomial (c2 has single coefficient)
    (|c2| == 1 && |c1| > 0) ==> 
      (|result| == |c1| && forall i :: 0 <= i < |c1| ==> result[i] == c1[i] * c2[0])
  ensures
    // Multiplication by constant polynomial (c1 has single coefficient)  
    (|c1| == 1 && |c2| > 0) ==> 
      (|result| == |c2| && forall i :: 0 <= i < |c2| ==> result[i] == c2[i] * c1[0])
  ensures
    // Zero polynomial property: if either input is all zeros, result is all zeros
    ((|c1| > 0 && forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) ||
     (|c2| > 0 && forall j :: 0 <= j < |c2| ==> c2[j] == 0.0)) ==>
      (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
  ensures
    // Result is never empty
    |result| >= 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): handle special cases (empty, zero-polynomial, constant multiplicands) early, then perform convolution with clear invariants using sum_prefix */
  if |c1| == 0 || |c2| == 0 {
    result := [0.0];
    return;
  }
  var m := |c1|;
  var n := |c2|;
  var len := m + n - 1;

  // If either polynomial is all zeros, return zero polynomial of correct length
  if (forall i :: 0 <= i < m ==> c1[i] == 0.0) || (forall j :: 0 <= j < n ==> c2[j] == 0.0) {
    var z := new real[len];
    var kk := 0;
    while kk < len
      invariant 0 <= kk <= len
      invariant forall t :: 0 <= t < kk ==> z[t] == 0.0
    {
      z[kk] := 0.0;
      kk := kk + 1;
    }
    result := z[..];
    return;
  }

  // Multiplication by constant polynomial c2
  if n == 1 {
    var a0 := new real[m];
    var ii := 0;
    while ii < m
      invariant 0 <= ii <= m
      invariant forall t :: 0 <= t < ii ==> a0[t] == c1[t] * c2[0]
    {
      a0[ii] := c1[ii] * c2[0];
      ii := ii + 1;
    }
    result := a0[..];
    return;
  }

  // Multiplication by constant polynomial c1
  if m == 1 {
    var a1 := new real[n];
    var jj := 0;
    while jj < n
      invariant 0 <= jj <= n
      invariant forall t :: 0 <= t < jj ==> a1[t] == c2[t] * c1[0]
    {
      a1[jj] := c2[jj] * c1[0];
      jj := jj + 1;
    }
    result := a1[..];
    return;
  }

  // General convolution
  var a := new real[len];
  var idx := 0;
  while idx < len
    invariant 0 <= idx <= len
    invariant forall p :: 0 <= p < idx ==> a[p] == 0.0
  {
    a[idx] := 0.0;
    idx := idx + 1;
  }

  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall p :: 0 <= p < len ==> a[p] == sum_prefix(c1, c2, p, i)
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall p :: 0 <= p < len ==> a[p] == sum_prefix(c1, c2, p, i) + (if 0 <= p - i < j then c1[i] * c2[p - i] else 0.0)
    {
      a[i + j] := a[i + j] + c1[i] * c2[j];
      j := j + 1;
    }
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
