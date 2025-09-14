function CountOccurrences(s: seq<int>, x: int): int
    ensures CountOccurrences(s, x) >= 0
    ensures CountOccurrences(s, x) <= |s|
{
    if |s| == 0 then 0
    else if s[0] == x then 1 + CountOccurrences(s[1..], x)
    else CountOccurrences(s[1..], x)
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

predicate ValidInput(n: int, ratings: seq<int>)
{
    n >= 2 && |ratings| == n
}

predicate AllInfected(k: int, ratings: seq<int>)
{
    k in ratings && CountOccurrences(ratings, k) == |ratings|
}

predicate CanInfectInOneContest(k: int, ratings: seq<int>)
{
    (k in ratings && CountOccurrences(ratings, k) != |ratings|) ||
    (k !in ratings && k * |ratings| == Sum(ratings))
}

predicate RequiresTwoContests(k: int, ratings: seq<int>)
{
    k !in ratings && k * |ratings| != Sum(ratings)
}

// <vc-helpers>
lemma CountOccurrencesAllElements(s: seq<int>, x: int)
    ensures (CountOccurrences(s, x) == |s|) <==> (forall i :: 0 <= i < |s| ==> s[i] == x)
{
    if |s| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        if CountOccurrences(s, x) == |s| {
            assert s[0] == x;
            CountOccurrencesAllElements(s[1..], x);
        } else {
            if s[0] != x {
                // First element is not x, so not all elements are x
            } else {
                // First element is x, but not all remaining elements are x
                CountOccurrencesAllElements(s[1..], x);
            }
        }
    }
}

lemma CountOccurrencesZeroImpliesNotIn(s: seq<int>, x: int)
    ensures CountOccurrences(s, x) == 0 <==> x !in s
{
    if |s| == 0 {
        // Base case
    } else {
        // Inductive case
        if s[0] == x {
            assert CountOccurrences(s, x) >= 1;
        } else {
            CountOccurrencesZeroImpliesNotIn(s[1..], x);
        }
    }
}

lemma CountOccurrencesPositiveImpliesIn(s: seq<int>, x: int)
    ensures CountOccurrences(s, x) > 0 <==> x in s
{
    CountOccurrencesZeroImpliesNotIn(s, x);
}
// </vc-helpers>

// <vc-spec>
method SolveCase(n: int, k: int, ratings: seq<int>) returns (answer: int)
    requires ValidInput(n, ratings)
    ensures answer >= 0 && answer <= 2
    ensures AllInfected(k, ratings) ==> answer == 0
    ensures CanInfectInOneContest(k, ratings) && !AllInfected(k, ratings) ==> answer == 1
    ensures RequiresTwoContests(k, ratings) ==> answer == 2
// </vc-spec>
// <vc-code>
{
    var count := CountOccurrences(ratings, k);
    
    if count == |ratings| {
        // All programmers already have rating k
        CountOccurrencesAllElements(ratings, k);
        assert AllInfected(k, ratings);
        return 0;
    } else if count > 0 {
        // Some but not all have rating k
        CountOccurrencesPositiveImpliesIn(ratings, k);
        assert k in ratings;
        assert CountOccurrences(ratings, k) != |ratings|;
        assert CanInfectInOneContest(k, ratings);
        return 1;
    } else {
        // No one has rating k
        CountOccurrencesZeroImpliesNotIn(ratings, k);
        assert k !in ratings;
        var sum := Sum(ratings);
        
        if k * |ratings| == sum {
            // Average equals k
            assert CanInfectInOneContest(k, ratings);
            return 1;
        } else {
            // Average doesn't equal k
            assert RequiresTwoContests(k, ratings);
            return 2;
        }
    }
}
// </vc-code>

