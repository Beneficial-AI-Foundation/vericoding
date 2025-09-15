// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)

  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
// </vc-spec>
// <vc-code>
{
  res := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |res| == if i == 0 then 0 else 2 * i - 1
    invariant forall k :: 0 <= k < |res| && k % 2 == 0 ==> res[k] == numbers[k/2]
    invariant forall k :: 0 <= k < |res| && k % 2 == 1 ==> res[k] == delimeter
  {
    if i > 0 {
      res := res + [delimeter];
    }
    res := res + [numbers[i]];
    i := i + 1;
  }
}
// </vc-code>
