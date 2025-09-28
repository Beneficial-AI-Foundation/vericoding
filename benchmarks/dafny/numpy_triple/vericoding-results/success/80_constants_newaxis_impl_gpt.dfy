// <vc-preamble>
// Represents the newaxis constant used for dimension expansion in NumPy
datatype NewAxis = newaxis

// Expands a 1D sequence to a column matrix (n × 1) using newaxis
// Models the behavior of a[:, np.newaxis] which converts a sequence of length n
// to a sequence of sequences where each inner sequence has length 1
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define singleton sequence constructor for 1-element rows */
function singleton<T>(x: T): seq<T>
  ensures |singleton(x)| == 1
  ensures singleton(x)[0] == x
{
  [x]
}

// </vc-helpers>

// <vc-spec>
method expandToColumn<T>(v: seq<T>, axis: NewAxis) returns (result: seq<seq<T>>)
  ensures |result| == |v|                                                    // Result has same number of rows as input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == 1               // Each row has exactly one element
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == v[i]           // Each row contains the corresponding input element
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build column by iterative concatenation, maintaining invariants */
  var r: seq<seq<T>> := [];
  var i: int := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> |r[j]| == 1
    invariant forall j :: 0 <= j < |r| ==> r[j][0] == v[j]
  {
    r := r + [ [ v[i] ] ];
    i := i + 1;
  }
  result := r;
}

// </vc-code>
