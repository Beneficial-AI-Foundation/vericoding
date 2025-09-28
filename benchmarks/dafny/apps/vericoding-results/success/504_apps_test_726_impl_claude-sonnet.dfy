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
lemma SumContributionsNonNegative(hotels: seq<int>, d: int, i: int)
    requires 0 <= i <= |hotels| - 1
    requires d > 0
    requires forall j :: 0 <= j < |hotels| - 1 ==> hotels[j] < hotels[j + 1]
    ensures SumContributions(hotels, d, i) >= 0
{
    if i == 0 {
        // Base case: SumContributions returns 0
    } else {
        // Inductive case
        var gap := hotels[i] - hotels[i-1];
        var contribution := if gap == 2*d then 1 else if gap > 2*d then 2 else 0;
        assert contribution >= 0;
        SumContributionsNonNegative(hotels, d, i-1);
        assert SumContributions(hotels, d, i-1) >= 0;
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
    result := 2;
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant result == 2 + SumContributions(hotels, d, i-1)
    {
        var gap := hotels[i] - hotels[i-1];
        if gap == 2*d {
            result := result + 1;
        } else if gap > 2*d {
            result := result + 2;
        }
        i := i + 1;
    }
    
    SumContributionsNonNegative(hotels, d, n-1);
}
// </vc-code>

