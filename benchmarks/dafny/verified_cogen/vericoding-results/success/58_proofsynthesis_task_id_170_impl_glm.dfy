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
/* helper modified by LLM (iteration 4): fix calc statement syntax */
lemma SumToExtend(arr: array<int>, start: int, i: int)
    requires 0 <= start <= i < arr.Length
    ensures SumTo(arr[start..i+1]) == SumTo(arr[start..i]) + arr[i]
{
    var s := arr[start..i+1];
    var n := |s|;
    if n == 0 {
        // impossible by precondition
    } else {
        assert s[n-1] == arr[i];
        var s_rest := s[0..n-1];
        assert s_rest == arr[start..i];
        calc {
            SumTo(s);
            ==
            SumTo(s_rest) + s[n-1];
            ==
            SumTo(arr[start..i]) + arr[i];
        }
    }
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
  var total := 0;
  while i <= end
    invariant start <= i <= end + 1
    invariant total == SumTo(arr[start..i])
  {
    SumToExtend(arr, start, i);
    total := total + arr[i];
    i := i + 1;
  }
  return total;
}
// </vc-code>
