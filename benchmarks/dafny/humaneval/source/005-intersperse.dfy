method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)
  // post-conditions-start
  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
  // post-conditions-end
{
  // impl-start
  res := [];
  if (|numbers| != 0)
  {
    for i := 0 to |numbers| - 1
      // invariants-start
      invariant |res| == 2 * i
      invariant forall i1 : int :: i1 >= 0 && i1 < |res| && i1 % 2 == 0 ==> res[i1] == numbers[i1 / 2]
      invariant forall i1 : int :: i1 >= 0 && i1 < |res| && i1 % 2 == 1 ==> res[i1] == delimeter
      // invariants-end
    {
      res := res + [numbers[i]];
      res := res + [delimeter];
    }
    res := res + [numbers[|numbers|-1]];
  }
  // impl-end
}
