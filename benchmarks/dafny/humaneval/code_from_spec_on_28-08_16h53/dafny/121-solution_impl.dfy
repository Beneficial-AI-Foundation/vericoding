// <vc-helpers>
predicate isOddAtEvenPosition(s: seq<int>, i: int)
{
  0 <= i < |s| && i % 2 == 0 && s[i] % 2 == 1
}

function oddAtEvenPositions(s: seq<int>) : seq<bool>
{
  seq(|s|, i => isOddAtEvenPosition(s, i))
}

lemma oddAtEvenPositionsLength(s: seq<int>)
  ensures |oddAtEvenPositions(s)| == |s|
{
}

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
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
  ensures result == sum(lst, oddAtEvenPositions(lst))
// </vc-spec>
// <vc-code>
method solution(lst: seq<int>) returns (result: int)
  requires |lst| > 0
  ensures result == sum(lst, oddAtEvenPositions(lst))
{
  oddAtEvenPositionsLength(lst);
  result := sum(lst, oddAtEvenPositions(lst));
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end