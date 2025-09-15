

// <vc-helpers>

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
    res := [];
    return;
  }
  var n := |numbers|;
  var m := n * 2 - 1;
  var a := new int[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i && j % 2 == 0 ==> a[j] == numbers[j / 2]
    invariant forall j :: 0 <= j < i && j % 2 == 1 ==> a[j] == delimeter
  {
    if i % 2 == 0 {
      a[i] := numbers[i / 2];
    } else {
      a[i] := delimeter;
    }
    i := i + 1;
  }
  res := a[..];
}
// </vc-code>

