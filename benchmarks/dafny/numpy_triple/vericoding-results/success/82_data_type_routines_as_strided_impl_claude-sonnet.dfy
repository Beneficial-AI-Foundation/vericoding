// <vc-preamble>
/*
 * Dafny specification for numpy.as_strided functionality.
 * Creates a view into an array with specified shape and strides,
 * accessing elements at regular stride intervals from the original array.
 */
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x[j * stride]
  {
    result := result + [x[i * stride]];
    i := i + 1;
  }
}
// </vc-code>
