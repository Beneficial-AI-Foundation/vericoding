

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
  } else {
    res := [];
    var i := 0;
    while i < |numbers|
      invariant 0 <= i <= |numbers|
      invariant |res| == if i == 0 then 0 else i * 2 - 1
      invariant forall j :: 0 <= j < |res| && j % 2 == 0 ==> res[j] == numbers[j / 2]
      invariant forall j :: 0 <= j < |res| && j % 2 == 1 ==> res[j] == delimeter
    {
      if i > 0 {
        res := res + [delimeter];
      }
      res := res + [numbers[i]];
      i := i + 1;
    }
  }
}
// </vc-code>

