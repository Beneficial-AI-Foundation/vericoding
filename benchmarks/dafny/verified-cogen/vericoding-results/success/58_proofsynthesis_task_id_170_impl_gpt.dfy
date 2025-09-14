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
lemma SumToSnocLemma(s: seq<int>, x: int)
  ensures SumTo(s + [x]) == SumTo(s) + x
{
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| > 0;
  assert (s + [x])[..|s + [x]| - 1] == s;
  assert (s + [x])[|s + [x]| - 1] == x;
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
  var i := start;
  sum := 0;
  while i <= end
    invariant start <= i <= end + 1
    invariant sum == SumTo(arr[start..i])
    decreases end - i + 1
  {
    assert i < arr.Length;
    assert |arr[start..i+1]| == i + 1 - start;
    assert |arr[start..i+1]| > 0;
    assert (arr[start..i+1])[..|arr[start..i+1]| - 1] == arr[start..i];
    assert (arr[start..i+1])[|arr[start..i+1]| - 1] == arr[i];
    sum := sum + arr[i];
    assert sum == SumTo(arr[start..i+1]);
    i := i + 1;
  }
}
// </vc-code>
