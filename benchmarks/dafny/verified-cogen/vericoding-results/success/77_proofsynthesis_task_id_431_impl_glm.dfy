// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed reads clause */
function Contains(arr: array<int>, x: int): bool reads arr {
  exists i: int :: 0 <= i < arr.Length && arr[i] == x
}
// </vc-helpers>

// <vc-spec>
method HasCommonElement(list1: array<int>, list2: array<int>) returns (result: bool)
    ensures
        result == (exists i: int, j: int ::
            0 <= i < list1.Length && 0 <= j < list2.Length && (list1[i] == list2[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): no change in method body */
  var i := 0;
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant forall k: int, l: int :: 0 <= k < i && 0 <= l < list2.Length ==> list1[k] != list2[l]
  {
    var j := 0;
    while j < list2.Length
      invariant 0 <= j <= list2.Length
      invariant forall l: int :: 0 <= l < j ==> list1[i] != list2[l]
    {
      if (list1[i] == list2[j]) {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
