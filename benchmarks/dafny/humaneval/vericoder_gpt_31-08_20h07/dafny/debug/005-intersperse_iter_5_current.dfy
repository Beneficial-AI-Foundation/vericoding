

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

      assert |prevRes| == 2 * prevI - 1;
      assert forall j: int :: 0 <= j && j < |prevRes| && j % 2 == 0 ==> prevRes[j] == numbers[j / 2];
      assert forall j: int :: 0 <= j && j < |prevRes| && j % 2 == 1 ==> prevRes[j] == delimeter;

      res := prevRes + [delimeter, numbers[prevI]];
      i := prevI + 1;

      assert |res| == |prevRes| + 2;
      assert |res| == 2 * i - 1;

      forall j: int | 0 <= j && j < |res| && j % 2 == 0
        ensures res[j] == numbers[j / 2]
      {
        if j < |prevRes| {
          assert res[j] == prevRes[j];
          assert 0 <= j && j < |prevRes| && j % 2 == 0;
          assert prevRes[j] == numbers[j / 2];
        } else {
          assert |prevRes| % 2 == 1;
          assert |res| == |prevRes| + 2;
          assert j >= |prevRes|;
          assert j <= |prevRes| + 1;
          assert j != |prevRes|;
          assert j == |prevRes| + 1;
          assert res[j] == [delimeter, numbers[prevI]][j - |prevRes|];
          assert j - |prevRes| == 1;
          assert res[j] == numbers[prevI];
          assert |prevRes| == 2 * prevI - 1;
          assert j == |prevRes| + 1;
          assert j == 2 * prevI;
          assert j / 2 == prevI;
          assert res[j] == numbers[j / 2];
        }
      }

      forall j: int | 0 <= j && j < |res| && j % 2 == 1
        ensures res[j] == delimeter
      {
        if j < |prevRes| {
          assert res[j] == prevRes[j];
          assert 0 <= j && j < |prevRes| && j % 2 == 1;
          assert prevRes[j] == delimeter;
        } else {
          assert |res| == |prevRes| + 2;
          assert j >= |prevRes|;
          assert j <= |prevRes| + 1;
          assert |prevRes| == 2 * prevI - 1;
          if j == |prevRes| {
            assert res[j] == [delimeter, numbers[prevI]][0];
            assert res[j] == delimeter;
          } else {
            assert j == |prevRes| + 1;
            assert j == 2 * prevI;
            assert j % 2 == 0;
            assert false;
          }
        }
      }
    }
  }
}
// </vc-code>

