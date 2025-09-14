predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>
lemma CountEligibleAppend(s: seq<int>, x: int, k: int)
  ensures CountEligible(s + [x], k) == CountEligible(s, k) + (if x >= k then 1 else 0)
{
  calc {
    CountEligible(s + [x], k);
    |set i | 0 <= i
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
lemma CountEligibleAppend(s: seq<int>, x: int, k: int)
  ensures CountEligible(s + [x], k) == CountEligible(s, k) + (if x >= k then 1 else 0)
{
  calc {
    CountEligible(s + [x], k);
    |set i | 0 <= i
// </vc-code>

