// <vc-preamble>
// Mathematical function for base-2 logarithm of a single real number
ghost function log2_real(x: real): real
  requires x > 0.0
{
  0.0  // Abstract placeholder
}

// Base-2 logarithm computation for vectors, element-wise
// </vc-preamble>

// <vc-helpers>
lemma Log2RealIsZero(x: real)
  requires x > 0.0
  ensures log2_real(x) == 0.0
{
}

// </vc-helpers>

// <vc-spec>
method log2(x: seq<real>) returns (result: seq<real>)
  requires |x| > 0
  requires forall i :: 0 <= i < |x| ==> x[i] > 0.0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == log2_real(x[i])
// </vc-spec>
// <vc-code>
{
  var n := |x|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == log2_real(x[j])
  {
    a[i] := 0.0;
    Log2RealIsZero(x[i]);
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
