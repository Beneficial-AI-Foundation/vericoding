// <vc-preamble>
function SumTo(arr: seq<int>): int
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        SumTo(arr[..|arr|-1]) + arr[|arr|-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): snoc property for SumTo */
lemma SeqSumSnoc(s: seq<int>, x: int)
  ensures SumTo(s + [x]) == SumTo(s) + x
{
  assert |s + [x]| > 0;
  assert SumTo(s + [x]) == SumTo((s + [x])[..|s + [x]|-1]) + (s + [x])[|s + [x]|-1];
  assert (s + [x])[|s + [x]|-1] == x;
  assert (s + [x])[..|s + [x]|-1] == s;
  assert SumTo((s + [x])[..|s + [x]|-1]) == SumTo(s);
  assert SumTo(s + [x]) == SumTo(s) + x;
}

/* helper modified by LLM (iteration 4): extend slice by one index */
lemma SumSliceExtend(arr: array<int>, start:int, i:int)
  requires 0 <= start <= i < arr.Length
  ensures SumTo(arr[start..i+1]) == SumTo(arr[start..i]) + arr[i]
{
  assert arr[start..i+1] == arr[start..i] + [arr[i]];
  SeqSumSnoc(arr[start..i], arr[i]);
  assert SumTo(arr[start..i+1]) == SumTo(arr[start..i]) + arr[i];
}
// </vc-helpers>

// <vc-spec>
method SumRangeList(arr: array<int>, start: int, end: int) returns (sum: int)
    requires 0 <= start <= end
    requires start <= end < arr.Length
    ensures SumTo(arr[start..end+1]) == sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): iterative summation using SumSliceExtend lemma */
  sum := 0;
  var i := start;
  while i <= end
    invariant start <= i <= end + 1
    invariant sum == SumTo(arr[start..i])
  {
    SumSliceExtend(arr, start, i);
    sum := sum + arr[i];
    i := i + 1;
  }
}

// </vc-code>
