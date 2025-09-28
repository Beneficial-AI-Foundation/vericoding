// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(list1: array<int>, list2: array<int>) returns (result: bool)
    ensures
        result == (exists i: int, j: int ::
            0 <= i < list1.Length && 0 <= j < list2.Length && (list1[i] == list2[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant to properly handle result updates */
  result := false;
  var i := 0;
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant result ==> (exists x: int, y: int :: 0 <= x < list1.Length && 0 <= y < list2.Length && list1[x] == list2[y])
    invariant !result ==> (forall x: int, y: int :: 0 <= x < i && 0 <= y < list2.Length ==> list1[x] != list2[y])
  {
    var j := 0;
    while j < list2.Length
      invariant 0 <= j <= list2.Length
      invariant result ==> (exists x: int, y: int :: 0 <= x < list1.Length && 0 <= y < list2.Length && list1[x] == list2[y])
      invariant !result ==> (forall y: int :: 0 <= y < j ==> list1[i] != list2[y])
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
