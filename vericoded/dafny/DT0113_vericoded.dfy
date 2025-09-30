// <vc-preamble>
// Represents the newaxis constant used for dimension expansion in NumPy
datatype NewAxis = newaxis

// Expands a 1D sequence to a column matrix (n × 1) using newaxis
// Models the behavior of a[:, np.newaxis] which converts a sequence of length n
// to a sequence of sequences where each inner sequence has length 1
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method expandToColumn<T>(v: seq<T>, axis: NewAxis) returns (result: seq<seq<T>>)
  ensures |result| == |v|                                                    // Result has same number of rows as input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == 1               // Each row has exactly one element
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == v[i]           // Each row contains the corresponding input element
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> |result[j]| == 1
    invariant forall j :: 0 <= j < |result| ==> result[j][0] == v[j]
  {
    result := result + [[v[i]]];
    i := i + 1;
  }
}
// </vc-code>
