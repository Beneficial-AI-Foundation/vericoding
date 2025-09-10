function wowFactor(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures wowFactor(s) >= 0
{
    if |s| < 4 then 0
    else
        var n := |s|;
        wowFactorSum(s, 0)
}

function countVVPairsBefore(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures countVVPairsBefore(s, pos) >= 0
{
    if pos <= 1 then 0
    else
        var prev := countVVPairsBefore(s, pos - 1);
        if s[pos-1] == 'v' && s[pos-2] == 'v' then prev + 1 else prev
}

function countVVPairsAfter(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures countVVPairsAfter(s, pos) >= 0
    decreases |s| - pos
{
    if pos >= |s| - 1 then 0
    else
        var rest := countVVPairsAfter(s, pos + 1);
        if pos + 1 < |s| && s[pos] == 'v' && s[pos+1] == 'v' then rest + 1 else rest
}

function wowFactorSum(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures wowFactorSum(s, pos) >= 0
    decreases |s| - pos
{
    if pos >= |s| then 0
    else
        var current := if s[pos] == 'o' then 
            countVVPairsBefore(s, pos) * countVVPairsAfter(s, pos + 1)
        else 0;
        current + wowFactorSum(s, pos + 1)
}

// <vc-helpers>
lemma wowFactorSumLemma(s: string, pos: int, i: int)
    requires 0 <= i <= |s|
    requires 0 <= pos <= i
    requires forall k :: 0 <= k < |s| ==> s[k] == 'v' || s[k] == 'o'
    ensures wowFactorSum(s, pos) == wowFactorSum(s, i) + wowFactorSum_range(s, pos, i)
{
}

lemma wowFactorSumSplit(s: string, pos: int, mid: int)
    requires 0 <= pos <= mid <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures wowFactorSum(s, pos) == wowFactorSum_range(s, pos, mid) + wowFactorSum(s, mid)
{
}

function wowFactorSum_range(s: string, from: int, to: int): int
    requires 0 <= from <= to <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures wowFactorSum_range(s, from, to) >= 0
    decreases to - from
{
    if from >= to then 0
    else
        var current := if s[from] == 'o' then 
            countVVPairsBefore(s, from) * countVVPairsAfter(s, from + 1)
        else 0;
        current + wowFactorSum_range(s, from + 1, to)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    ensures result >= 0
    ensures result == wowFactor(s)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var n := |s|;
    var vvCountLeft := 0;
    var vvCountRight := countVVPairsAfter(s, 0);
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant vvCountLeft == countVVPairsBefore(s, i)
        invariant vvCountRight == countVVPairsAfter(s, i)
        invariant result == wowFactorSum(s, i)
    {
        if s[i] == 'o' {
            result := result + vvCountLeft * vvCountRight;
        }
        
        if i > 0 && s[i-1] == 'v' && s[i] == 'v' {
            vvCountLeft := vvCountLeft + 1;
        }
        
        if i < n - 1 && s[i] == 'v' && s[i+1] == 'v' {
            vvCountRight := vvCountRight - 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>

