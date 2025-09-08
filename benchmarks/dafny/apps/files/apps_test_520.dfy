Given a list of university entrance years for groups that student Igor joined,
determine Igor's university entrance year. Igor joins his own group and all groups
where the entrance year differs by at most x years from his entrance year.
The solution computes Igor's entrance year as the average of all group years.

function sumRange(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start == end then 0
    else s[start] + sumRange(s, start + 1, end)
}

predicate ValidInput(n: int, years: seq<int>)
{
    n > 0 && |years| == n
}

lemma sumRangeLemma(s: seq<int>, start: int, end: int)
    requires 0 <= start < end <= |s|
    ensures sumRange(s, start, end - 1) + s[end - 1] == sumRange(s, start, end)
    decreases end - start
{
    if start == end - 1 {
        // Base case: sumRange(s, start, start) + s[start] == sumRange(s, start, start + 1)
        // sumRange(s, start, start) is 0, so we need 0 + s[start] == sumRange(s, start, start + 1)
        // sumRange(s, start, start + 1) is s[start] by definition
    } else {
        // Recursive case: sumRange(s, start, end - 1) + s[end - 1] == sumRange(s, start, end)
        // Both sides expand to s[start] + (sumRange(s, start + 1, end - 1) + s[end - 1]) 
        // and s[start] + sumRange(s, start + 1, end) respectively
        // By induction: sumRange(s, start + 1, end - 1) + s[end - 1] == sumRange(s, start + 1, end)
        sumRangeLemma(s, start + 1, end);
    }
}

method solve(n: int, years: seq<int>) returns (result: int)
    requires ValidInput(n, years)
    ensures result == sumRange(years, 0, |years|) / n
{
    var sum := 0;
    var i := 0;
    while i < |years|
        invariant 0 <= i <= |years|
        invariant sum == sumRange(years, 0, i)
    {
        sum := sum + years[i];
        i := i + 1;
        sumRangeLemma(years, 0, i);
    }
    result := sum / n;
}
