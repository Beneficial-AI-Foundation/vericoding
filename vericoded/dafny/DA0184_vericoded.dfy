predicate ValidInput(n: int, c: int, P: seq<int>, T: seq<int>)
{
    n > 0 && c > 0 && |P| == n && |T| == n &&
    (forall i :: 0 <= i < n ==> P[i] > 0) &&
    (forall i :: 0 <= i < n ==> T[i] > 0) &&
    (forall i :: 0 <= i < n-1 ==> P[i] < P[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> T[i] < T[i+1])
}

function calculateLimakScore(n: int, c: int, P: seq<int>, T: seq<int>): int
    requires n > 0 && |P| == n && |T| == n
{
    if n == 0 then 0
    else 
        var cumulativeTime := sum(T[..1]);
        var score := if P[0] - c * cumulativeTime > 0 then P[0] - c * cumulativeTime else 0;
        score + calculateLimakScoreHelper(n-1, c, P[1..], T[1..], cumulativeTime)
}

function calculateLimakScoreHelper(remaining: int, c: int, P: seq<int>, T: seq<int>, prevTime: int): int
    requires remaining >= 0 && |P| == remaining && |T| == remaining
{
    if remaining == 0 then 0
    else 
        var cumulativeTime := prevTime + T[0];
        var score := if P[0] - c * cumulativeTime > 0 then P[0] - c * cumulativeTime else 0;
        score + calculateLimakScoreHelper(remaining-1, c, P[1..], T[1..], cumulativeTime)
}

function calculateRadewooshScore(n: int, c: int, P: seq<int>, T: seq<int>): int
    requires n > 0 && |P| == n && |T| == n
{
    calculateRadewooshScoreHelper(n, c, P, T, 0)
}

function calculateRadewooshScoreHelper(remaining: int, c: int, P: seq<int>, T: seq<int>, prevTime: int): int
    requires remaining >= 0 && |P| >= remaining && |T| >= remaining
{
    if remaining == 0 then 0
    else 
        var idx := remaining - 1;
        var cumulativeTime := prevTime + T[idx];
        var score := if P[idx] - c * cumulativeTime > 0 then P[idx] - c * cumulativeTime else 0;
        score + calculateRadewooshScoreHelper(remaining-1, c, P, T, cumulativeTime)
}

// <vc-helpers>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, c: int, P: seq<int>, T: seq<int>) returns (result: string)
    requires ValidInput(n, c, P, T)
    ensures result == "Limak" || result == "Radewoosh" || result == "Tie"
    ensures var limakScore := calculateLimakScore(n, c, P, T);
            var radewooshScore := calculateRadewooshScore(n, c, P, T);
            (result == "Limak" <==> limakScore > radewooshScore) &&
            (result == "Radewoosh" <==> limakScore < radewooshScore) &&
            (result == "Tie" <==> limakScore == radewooshScore)
// </vc-spec>
// <vc-code>
{
    var limakScore := calculateLimakScore(n, c, P, T);
    var radewooshScore := calculateRadewooshScore(n, c, P, T);
    
    if limakScore > radewooshScore {
        result := "Limak";
    } else if limakScore < radewooshScore {
        result := "Radewoosh";
    } else {
        result := "Tie";
    }
}
// </vc-code>

