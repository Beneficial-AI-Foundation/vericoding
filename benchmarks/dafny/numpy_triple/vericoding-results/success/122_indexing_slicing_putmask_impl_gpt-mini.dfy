// <vc-preamble>
/*
 * Dafny specification for numpy.putmask functionality.
 * Changes elements of an array based on conditional and input values,
 * with cyclic repetition of values when the values array is smaller.
 */
// </vc-preamble>

// <vc-helpers>
lemma ModRange(i: int, m: int)
  requires m > 0
  ensures 0 <= i % m < m
{
  var r := i % m;
  assert 0 <= r;
  assert r < m;
}

// </vc-helpers>

// <vc-spec>
method putmask(a: seq<real>, mask: seq<bool>, values: seq<real>) returns (result: seq<real>)
    // Preconditions: arrays must have same length, values must be non-empty
    requires |a| == |mask|
    requires |values| > 0
    
    // Postconditions: specify the exact behavior of putmask
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> result[i] == values[i % |values|])
    ensures forall i :: 0 <= i < |result| ==> 
        (!mask[i] ==> result[i] == a[i])
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> exists j :: 0 <= j < |values| && result[i] == values[j])
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var m := |values|;
  var A := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> (mask[k] ==> A[k] == values[k % m]) && (!mask[k] ==> A[k] == a[k])
  {
    if mask[i] {
      A[i] := values[i % m];
    } else {
      A[i] := a[i];
    }
    i := i + 1;
  }
  result := A[..];
}

// </vc-code>
