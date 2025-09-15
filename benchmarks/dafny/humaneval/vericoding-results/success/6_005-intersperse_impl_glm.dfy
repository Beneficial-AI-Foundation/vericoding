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
  /* code modified by LLM (iteration 3): Added loop invariants to prove postconditions */
  if |numbers| == 0 {
    return [];
  }
  res := [numbers[0]];
  for i := 1 to |numbers|
    invariant 1 <= i <= |numbers|
    invariant |res| == 2 * i - 1
    invariant forall j: int :: 0 <= j < |res| && j % 2 == 0 ==> res[j] == numbers[j/2]
    invariant forall j: int :: 0 <= j < |res| && j % 2 == 1 ==> res[j] == delimeter
  {
    res := res + [delimeter, numbers[i]];
  }
  return res;
}
// </vc-code>
