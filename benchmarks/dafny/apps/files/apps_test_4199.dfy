Count how many people can ride a roller coaster given their heights and a minimum height requirement.
Input: N (number of people), K (minimum height requirement), and N heights.
Output: Number of people who can ride (height >= K).

predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
{
    count := 0;
    var i := 0;
    while i < |heights|
        invariant 0 <= i <= |heights|
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && heights[j] >= k :: j|
    {
        if heights[i] >= k {
            assert i in (set j | 0 <= j < i + 1 && heights[j] >= k :: j);
            assert i !in (set j | 0 <= j < i && heights[j] >= k :: j);
            assert (set j | 0 <= j < i + 1 && heights[j] >= k :: j) == (set j | 0 <= j < i && heights[j] >= k :: j) + {i};
            count := count + 1;
        } else {
            assert i !in (set j | 0 <= j < i + 1 && heights[j] >= k :: j);
            assert (set j | 0 <= j < i + 1 && heights[j] >= k :: j) == (set j | 0 <= j < i && heights[j] >= k :: j);
        }
        i := i + 1;
    }
}
