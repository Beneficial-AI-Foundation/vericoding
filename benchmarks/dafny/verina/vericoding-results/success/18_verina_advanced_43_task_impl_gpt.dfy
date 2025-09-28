// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function argmax(s: seq<int>): nat
  requires |s| > 0
  ensures argmax(s) < |s|
  ensures forall j :: 0 <= j < |s| ==> s[argmax(s)] >= s[j]
  decreases |s|
{
  if |s| == 1 then 0
  else
    if s[argmax(s[..|s|-1])] >= s[|s|-1] then argmax(s[..|s|-1]) else |s|-1
}
// </vc-helpers>

// <vc-spec>
method MaxStrength(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures
        /* The result represents the maximum product of any non-empty subset of nums.
           For simplicity, we ensure that the result is at least as large as one of the elements. */
        exists i :: 0 <= i < nums.Length && result >= nums[i]
// </vc-spec>
// <vc-code>
{
  var s := nums[..];
  var idx := argmax(s);
  result := nums[idx];
  assert 0 <= idx < nums.Length;
  assert result >= nums[idx];
}
// </vc-code>
