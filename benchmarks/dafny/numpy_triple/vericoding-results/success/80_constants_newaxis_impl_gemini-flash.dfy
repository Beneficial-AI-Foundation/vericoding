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
/* code modified by LLM (iteration 5): Fixed loop bound and added post-loop assertions to ensure all ensures clauses are met. */
{
  var temp_res: seq<seq<T>> := [];
  for i := 0 to |v|
    invariant 0 <= i <= |v|
    invariant |temp_res| == i
    invariant forall j :: 0 <= j < i ==> |temp_res[j]| == 1
    invariant forall j :: 0 <= j < i ==> temp_res[j][0] == v[j]
  {
    if i < |v| {
      temp_res := temp_res + [[v[i]]];
    }
  }
  assert |temp_res| == |v|;
  assert forall i_idx :: 0 <= i_idx < |temp_res| ==> |temp_res[i_idx]| == 1;
  assert forall i_idx :: 0 <= i_idx < |temp_res| ==> temp_res[i_idx][0] == v[i_idx];
  return temp_res;
}
// </vc-code>
