// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): reads clause added to allow array element access */
function ElemIn(arr: array<int>, x: int): bool reads arr { exists i :: 0 <= i < arr.Length && arr[i] == x }
// </vc-helpers>

// <vc-spec>
method HasCommonElement(list1: array<int>, list2: array<int>) returns (result: bool)
    ensures
        result == (exists i: int, j: int ::
            0 <= i < list1.Length && 0 <= j < list2.Length && (list1[i] == list2[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative search with loop invariants proving absence/presence of common element */
  var i := 0;
  result := false;
  while i < list1.Length
    decreases list1.Length - i
    invariant 0 <= i <= list1.Length
    invariant (forall k :: 0 <= k < i ==> forall l :: 0 <= l < list2.Length ==> list1[k] != list2[l])
  {
    var j := 0;
    while j < list2.Length
      decreases list2.Length - j
      invariant 0 <= j <= list2.Length
      invariant (forall l :: 0 <= l < j ==> list1[i] != list2[l])
    {
      if list1[i] == list2[j] {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
