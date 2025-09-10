predicate ValidInput(n: int, d: int, hotels: seq<int>)
{
    n > 0 && d > 0 && |hotels| == n &&
    (forall i :: 0 <= i < n - 1 ==> hotels[i] < hotels[i + 1])
}

function SumContributions(hotels: seq<int>, d: int, i: int): int
    requires 0 <= i <= |hotels| - 1
    requires d > 0
    requires forall j :: 0 <= j < |hotels| - 1 ==> hotels[j] < hotels[j + 1]
{
    if i == 0 then 0
    else
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        contribution + SumContributions(hotels, d, i-1)
}

predicate CorrectResult(n: int, d: int, hotels: seq<int>, result: int)
    requires ValidInput(n, d, hotels)
{
    result == 2 + SumContributions(hotels, d, n-1) && result >= 2
}

// <vc-helpers>
function SumContributionsAcc(hotels: seq<int>, d: int, i: int, acc: int): int
    requires -1 <= i < |hotels|
    requires d > 0
    requires forall j :: 0 <= j < |hotels| - 1 ==> hotels[j] < hotels[j + 1]
    decreases i
{
    if i == 0 then acc
    else
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        SumContributionsAcc(hotels, d, i-1, acc + contribution)
}

lemma SumContributionsAcc_equals_SumContributions(hotels: seq<int>, d: int, i: int)
    requires 0 <= i < |hotels|
    requires d > 0
    requires forall j :: 0 <= j < |hotels| - 1 ==> hotels[j] < hotels[j + 1]
    ensures SumContributionsAcc(hotels, d, i, 0) == SumContributions(hotels, d, i)
{
    if i == 0 {
    } else {
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        SumContributionsAcc_equals_SumContributions(hotels, d, i-1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, hotels: seq<int>) returns (result: int)
    requires ValidInput(n, d, hotels)
    ensures CorrectResult(n, d, hotels, result)
// </vc-spec>
// <vc-code>
{
    var current_sum_contributions := 0;
    for i := 1 to n - 1
        invariant 1 <= i <= n
        invariant current_sum_contributions == SumContributionsAcc(hotels, d, i - 1, 0)
        decreases n - i
    {
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        current_sum_contributions := current_sum_contributions + contribution;
    }
    lemma SumContributionsAcc_equals_SumContributions(hotels, d, n - 1);
    result := 2 + current_sum_contributions;
}
// </vc-code>

