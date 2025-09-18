// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function LISLength(s: seq<int>): nat
{
  if |s| == 0 then 0
  else
    var lastElement := s[|s|-1];
    var restLIS := LISLength(s[..|s|-1]);
    var extendedLIS := 1 + LISEndingWith(s[..|s|-1], lastElement);
    if extendedLIS > restLIS then extendedLIS else restLIS
}

function LISEndingWith(s: seq<int>, target: int): nat
{
  if |s| == 0 then 0
  else
    var lastElement := s[|s|-1];
    var restLIS := LISEndingWith(s[..|s|-1], target);
    if lastElement < target then
      var extendedLIS := 1 + LISEndingWith(s[..|s|-1], lastElement);
      if extendedLIS > restLIS then extendedLIS else restLIS
    else
      restLIS
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
  if nums.Length == 0 {
    result := 0;
  } else {
    result := LISLength(nums[..]);
  }
}
// </vc-code>
