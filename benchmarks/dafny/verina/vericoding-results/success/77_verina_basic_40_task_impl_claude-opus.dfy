// <vc-preamble>
predicate SecondSmallestPrecond(s: array<int>)
    reads s
{
    s.Length > 1
}

predicate SecondSmallestPostcond(s: array<int>, result: int)
    reads s
{
    (exists i :: 0 <= i < s.Length && s[i] == result) &&
    (exists j :: 0 <= j < s.Length && s[j] < result &&
        (forall k :: 0 <= k < s.Length && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added missing helper functions for finding minimum and second minimum */
function FindMin(s: array<int>, start: int, end: int): int
    requires 0 <= start < end <= s.Length
    requires s.Length > 0
    reads s
    decreases end - start
{
    if start + 1 == end then
        s[start]
    else
        var mid := start + (end - start) / 2;
        var leftMin := FindMin(s, start, mid);
        var rightMin := FindMin(s, mid, end);
        if leftMin <= rightMin then leftMin else rightMin
}

function FindSecondMin(s: array<int>, start: int, end: int, firstMin: int): int
    requires 0 <= start < end <= s.Length
    requires s.Length > 0
    reads s
    decreases end - start
{
    if start + 1 == end then
        if s[start] != firstMin then s[start] else s[start]
    else
        var mid := start + (end - start) / 2;
        var leftSecond := FindSecondMin(s, start, mid, firstMin);
        var rightSecond := FindSecondMin(s, mid, end, firstMin);
        if leftSecond == firstMin then rightSecond
        else if rightSecond == firstMin then leftSecond
        else if leftSecond <= rightSecond then leftSecond else rightSecond
}
// </vc-helpers>

// <vc-spec>
function SecondSmallest(s: array<int>): int
    requires SecondSmallestPrecond(s)
    reads s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed implementation to properly find second smallest element */
{
    var firstMin := FindMin(s, 0, s.Length);
    
    var hasDistinct := exists i :: 0 <= i < s.Length && s[i] != firstMin;
    
    if hasDistinct then
        FindSecondMin(s, 0, s.Length, firstMin)
    else
        firstMin
}
// </vc-code>
