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
  result := false;
  var i := 0;
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant !result ==> forall k: int, j: int :: 0 <= k < i && 0 <= j < list2.Length ==> list1[k] != list2[j]
    invariant result ==> exists k: int, j: int :: 0 <= k < list1.Length && 0 <= j < list2.Length && list1[k] == list2[j]
  {
    var j := 0;
    while j < list2.Length
      invariant 0 <= j <= list2.Length
      invariant !result ==> forall k: int, m: int :: 0 <= k < i && 0 <= m < list2.Length ==> list1[k] != list2[m]
      invariant !result ==> forall m: int :: 0 <= m < j ==> list1[i] != list2[m]
      invariant result ==> exists k: int, m: int :: 0 <= k < list1.Length && 0 <= m < list2.Length && list1[k] == list2[m]
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
