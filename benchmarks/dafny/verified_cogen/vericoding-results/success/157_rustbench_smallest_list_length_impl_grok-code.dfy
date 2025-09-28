// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement loop to find min length with invariants for verification */
  var minLen := lists[0].Length;
  var minIdx := 0;
  var i := 1;
  while i < lists.Length
    invariant 0 <= i <= lists.Length
    invariant forall k | 0 <= k < i :: minLen <= lists[k].Length
    invariant 0 <= minIdx < i
    invariant minLen == lists[minIdx].Length
  {
    if lists[i].Length < minLen {
      minLen := lists[i].Length;
      minIdx := i;
    }
    i := i + 1;
  }
  result := minLen;
}
// </vc-code>
