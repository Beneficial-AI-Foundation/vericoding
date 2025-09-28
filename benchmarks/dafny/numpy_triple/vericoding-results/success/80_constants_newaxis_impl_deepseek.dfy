// <vc-preamble>
// Represents the newaxis constant used for dimension expansion in NumPy
datatype NewAxis = newaxis

// Expands a 1D sequence to a column matrix (n × 1) using newaxis
// Models the behavior of a[:, np.newaxis] which converts a sequence of length n
// to a sequence of sequences where each inner sequence has length 1
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added equality constraint to type parameter */
  predicate IsColumnMatrix<T(==)>(m: seq<seq<T>>, original: seq<T>)
    requires |m| == |original|
  {
    (forall i :: 0 <= i < |m| ==> |m[i]| == 1)
    && (forall i :: 0 <= i < |m| ==> m[i][0] == original[i])
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
  /* code modified by LLM (iteration 3): Maintained correct implementation */
  result := seq(|v|, i requires 0 <= i < |v| => [v[i]]);
}
// </vc-code>
