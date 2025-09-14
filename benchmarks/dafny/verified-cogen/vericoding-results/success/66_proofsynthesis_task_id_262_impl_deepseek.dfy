// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqFromArray<T>(a: array<T>, start: int, end: int): seq<T>
  requires 0 <= start <= end <= a.Length
  decreases end - start
  reads a
{
  if start >= end then [] else [a[start]] + SeqFromArray(a, start + 1, end)
}
/* helper modified by LLM (iteration 4): Added decreases clause to fix termination error */
// </vc-helpers>

// <vc-spec>
method SplitArray(list: array<int>, l: int) returns (new_list: (seq<int>, seq<int>))
    requires
        list.Length > 0 &&
        0 < l < list.Length
    ensures
        new_list.0 == list[0..l] &&
        new_list.1 == list[l..list.Length]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Fixed code remains the same */
  var left := list[0..l];
  var right := list[l..list.Length];
  return (left, right);
}
// </vc-code>
