// <vc-preamble>
/*
 * Dafny specification for numpy.as_strided functionality.
 * Creates a view into an array with specified shape and strides,
 * accessing elements at regular stride intervals from the original array.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide ElemAt helper returning element at index */
function ElemAt(x: seq<real>, idx: nat): real
  requires idx < |x|
  ensures ElemAt(x, idx) == x[idx]
{
  x[idx]
}
// </vc-helpers>

// <vc-spec>
method AsStrided(x: seq<real>, m: nat, stride: nat) returns (result: seq<real>)
  // Preconditions: Valid bounds and positive stride
  requires m * stride <= |x|
  requires stride > 0
  
  // Postconditions: Result has correct size and elements are strided from original
  ensures |result| == m
  ensures forall i :: 0 <= i < m ==> result[i] == x[i * stride]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build strided sequence by populating an array with loop and invariants */
  var a := new real[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> a[j] == x[j * stride]
  {
    a[i] := x[i * stride];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
