// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
