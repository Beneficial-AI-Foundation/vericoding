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
lemma InRatingsImpliesCountAtLeastOne(k: int, ratings: seq<int>)
    requires k in ratings
    ensures CountOccurrences(ratings, k) >= 1
{
    if |ratings| > 0 {
        if ratings[0] == k {
            assert CountOccurrences(ratings, k) >= 1;
        } else {
            InRatingsImpliesCountAtLeastOne(k, ratings[1..]);
        }
    }
}

lemma CountLessThanLengthWhenNotAll(k: int, ratings: seq<int>)
    requires k in ratings
    requires CountOccurrences(ratings, k) != |ratings|
    ensures CountOccurrences(ratings, k) < |ratings|
{
    InRatingsImpliesCountAtLeastOne(k, ratings);
}

lemma ExclusiveConditions(k: int, ratings: seq<int>)
    requires ValidInput(|ratings|, ratings)
    ensures AllInfected(k, ratings) ==> !CanInfectInOneContest(k, ratings) && !RequiresTwoContests(k, ratings)
    ensures CanInfectInOneContest(k, ratings) ==> !AllInfected(k, ratings) && !RequiresTwoContests(k, ratings)
    ensures RequiresTwoContests(k, ratings) ==> !AllInfected(k, ratings) && !CanInfectInOneContest(k, ratings)
{
    if AllInfected(k, ratings) {
        assert k in ratings;
        assert CountOccurrences(ratings, k) == |ratings|;
        assert !((k in ratings && CountOccurrences(ratings, k) != |ratings|) ||
                (k !in ratings && k * |ratings| == Sum(ratings)));
        assert !(k !in ratings && k * |ratings| != Sum(ratings));
    } else if CanInfectInOneContest(k, ratings) {
        if k in ratings && CountOccurrences(ratings, k) != |ratings| {
            assert !AllInfected(k, ratings);
            assert !(k !in ratings && k * |ratings| != Sum(ratings));
        } else if k !in ratings && k * |ratings| == Sum(ratings) {
            assert !AllInfected(k, ratings);
            assert !(k !in ratings && k * |ratings| != Sum(ratings));
        }
    } else if RequiresTwoContests(k, ratings) {
        assert k !in ratings;
        assert !AllInfected(k, ratings);
        assert !CanInfectInOneContest(k, ratings);
    }
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
    ExclusiveConditions(k, ratings);
    
    if AllInfected(k, ratings) {
        answer := 0;
    } else if CanInfectInOneContest(k, ratings) {
        answer := 1;
    } else {
        answer := 2;
    }
}
// </vc-code>

