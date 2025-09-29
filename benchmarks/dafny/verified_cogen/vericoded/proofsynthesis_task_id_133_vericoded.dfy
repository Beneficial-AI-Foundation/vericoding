// <vc-preamble>
function SumNegativeTo(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        SumNegativeTo(s[..|s|-1]) + if (s[|s|-1] < 0) then
            s[|s|-1]
        else
            0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove loop invariant maintenance */
lemma SumNegativeToAppend(s: seq<int>, x: int)
  ensures SumNegativeTo(s + [x]) == SumNegativeTo(s) + if x < 0 then x else 0
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
  }
}
// </vc-helpers>

// <vc-spec>
method SumNegatives(arr: array<int>) returns (sum_neg: int)
    ensures SumNegativeTo(arr[..]) == sum_neg
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added lemma call to maintain loop invariant */
{
  sum_neg := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant sum_neg == SumNegativeTo(arr[..i])
  {
    var old_sum := sum_neg;
    if arr[i] < 0 {
      sum_neg := sum_neg + arr[i];
    }
    assert arr[..i+1] == arr[..i] + [arr[i]];
    SumNegativeToAppend(arr[..i], arr[i]);
    i := i + 1;
  }
  assert arr[..i] == arr[..arr.Length] == arr[..];
}
// </vc-code>
