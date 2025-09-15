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
/* code modified by LLM (iteration 3): corrected invariant for `res_seq` length */
{
  if |numbers| == 0 {
    return [];
  }

  var res_seq: seq<int> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant (i == 0 && |res_seq| == 0) || (i > 0 && |res_seq| == i * 2 - 1)
    invariant forall k : int :: 0 <= k < |res_seq| && k % 2 == 0 ==> res_seq[k] == numbers[k / 2]
    invariant forall k : int :: 0 <= k < |res_seq| && k % 2 == 1 ==> res_seq[k] == delimeter
  {
    if i > 0 {
      res_seq := res_seq + [delimeter];
    }
    res_seq := res_seq + [numbers[i]];
    i := i + 1;
  }
  res := res_seq;
}
// </vc-code>
