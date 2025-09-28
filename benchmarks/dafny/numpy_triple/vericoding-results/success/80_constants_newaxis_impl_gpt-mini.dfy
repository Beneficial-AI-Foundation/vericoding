// <vc-preamble>
// Represents the newaxis constant used for dimension expansion in NumPy
datatype NewAxis = newaxis

// Expands a 1D sequence to a column matrix (n × 1) using newaxis
// Models the behavior of a[:, np.newaxis] which converts a sequence of length n
// to a sequence of sequences where each inner sequence has length 1
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): create singleton sequence containing one element */
function singleton<T>(x: T): seq<T> { [x] }
// </vc-helpers>

// <vc-spec>
method expandToColumn<T>(v: seq<T>, axis: NewAxis) returns (result: seq<seq<T>>)
  ensures |result| == |v|                                                    // Result has same number of rows as input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == 1               // Each row has exactly one element
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == v[i]           // Each row contains the corresponding input element
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implement expandToColumn by building result sequentially */
{
  var res: seq<seq<T>> := [];
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> |res[j]| == 1
    invariant forall j :: 0 <= j < i ==> res[j][0] == v[j]
  {
    res := res + [ singleton(v[i]) ];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
