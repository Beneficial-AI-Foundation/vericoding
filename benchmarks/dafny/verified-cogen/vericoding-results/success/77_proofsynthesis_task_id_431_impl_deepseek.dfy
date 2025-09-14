// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function hasElement(list: array<int>, elem: int): bool
  reads list
  ensures hasElement(list, elem) == (exists j: int :: 0 <= j < list.Length && list[j] == elem)
{
  if list.Length == 0 then
    false
  else
    exists j: int :: 0 <= j < list.Length && list[j] == elem
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
  /* code modified by LLM (iteration 4): Remove null checks and use proper logic */
  result := exists i: int, j: int ::
    0 <= i < list1.Length && 0 <= j < list2.Length && (list1[i] == list2[j]);
}
// </vc-code>
