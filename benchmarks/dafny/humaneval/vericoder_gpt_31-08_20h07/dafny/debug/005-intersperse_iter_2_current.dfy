

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
    res := [];
  } else {
    res := [numbers[0]];
    var i := 1;
    while i < |numbers|
      invariant 1 <= i <= |numbers|
      invariant |res| == 2 * i - 1
      invariant forall j: int :: 0 <= j && j < |res| && j % 2 == 0 ==> res[j] == numbers[j / 2]
      invariant forall j: int :: 0 <= j && j < |res| && j % 2 == 1 ==> res[j] == delimeter
      decreases |numbers| - i
    {
      var prevRes := res;
      var prevI := i;

      res := prevRes + [delimeter, numbers[prevI]];
      i := prevI + 1;

      assert |res| == |prevRes| + 2;
      assert |prevRes| == 2 * prevI - 1;
      assert |res| == 2 * i - 1;

      assert forall j: int
        | 0 <= j && j < |res| && j % 2 == 0
        ensures res[j] == numbers[j / 2]
      {
        if j < |prevRes| {
          assert res[j] == prevRes[j];
        } else {
          assert |prevRes| % 2 == 1;
          assert j <= |prevRes| + 1;
          assert j != |prevRes|;
          assert j == |prevRes| + 1;
          assert res[j] == [delimeter, numbers[prevI]][j - |prevRes|];
          assert j - |prevRes| == 1;
          assert res[j] == numbers[prevI];
          assert j / 2 == prevI;
        }
      };

      assert forall j: int
        | 0 <= j && j < |res| && j % 2 == 1
        ensures res[j] == delimeter
      {
        if j < |prevRes| {
          assert res[j] == prevRes[j];
        } else {
          assert |prevRes| % 2 == 1;
          assert j <= |prevRes| + 1;
          assert j == |prevRes|;
          assert res[j] == [delimeter, numbers[prevI]][0];
          assert res[j] == delimeter;
        }
      };
    }
  }
}
// </vc-code>

