// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def solution(lst: List[int]) -> int
Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
*/
// </vc-description>

// <vc-spec>
method solution(lst: seq<int>) returns (result: int)
  requires |lst| > 0
  ensures result == sum(lst, seq(|lst|, i => i % 2 == 0 && lst[i] % 2 == 1))
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result == sum(lst[..i], seq(i, j => j % 2 == 0 && lst[j] % 2 == 1))
  {
    if i % 2 == 0 && lst[i] % 2 == 1 {
      result := result + lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end