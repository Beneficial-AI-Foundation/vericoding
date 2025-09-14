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
/* helper modified by LLM (iteration 3): added lemma to prove SumNegativeTo extension property */
lemma SumNegativeToExtend(s: seq<int>, x: int)
  ensures SumNegativeTo(s + [x]) == SumNegativeTo(s) + (if x < 0 then x else 0)
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert SumNegativeTo([x]) == (if x < 0 then x else 0);
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
    assert (s + [x])[|s + [x]| - 1] == x;
  }
}
// </vc-helpers>

// <vc-spec>
method SumNegatives(arr: array<int>) returns (sum_neg: int)
    ensures SumNegativeTo(arr[..]) == sum_neg
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed to ensure postcondition holds */
{
  sum_neg := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant sum_neg == SumNegativeTo(arr[..i])
  {
    if arr[i] < 0 {
      sum_neg := sum_neg + arr[i];
    }
    SumNegativeToExtend(arr[..i], arr[i]);
    assert arr[..i+1] == arr[..i] + [arr[i]];
    i := i + 1;
  }
  assert i == arr.Length;
  assert arr[..i] == arr[..];
}
// </vc-code>
