

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)
  // post-conditions-start
  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    return [];
  }
  var n := |numbers|;
  var result := new int[n * 2 - 1];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall k: int :: 0 <= k < i ==> result[2 * k] == numbers[k]
    invariant forall k: int :: 0 <= k < i ==> k < n - 1 ==> result[2 * k + 1] == delimeter
  {
    result[2 * i] := numbers[i];
    if i < n - 1 {
      result[2 * i + 1] := delimeter;
    }
  }
  assert forall j: int :: 0 <= j < |result| && j % 2 == 1 ==> result[j] == delimeter;
  return result;
}
// </vc-code>

