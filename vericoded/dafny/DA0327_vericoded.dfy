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
lemma WowFactorSumCorrect(s: string, pos: int, beforeCount: int, result: int)
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'v' || s[i] == 'o'
    requires beforeCount == countVVPairsBefore(s, pos)
    requires result >= 0
    ensures wowFactorSum(s, pos) >= 0
{
    // This lemma helps establish that wowFactorSum is always non-negative
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
    if |s| < 4 {
        return 0;
    }
    
    var pos := 0;
    var sum := 0;
    var vvBefore := 0;
    
    // First pass: calculate wowFactorSum
    while pos < |s|
        invariant 0 <= pos <= |s|
        invariant sum >= 0
        invariant vvBefore >= 0
        invariant vvBefore == countVVPairsBefore(s, pos)
        invariant sum == wowFactorSum(s, 0) - wowFactorSum(s, pos)
    {
        if s[pos] == 'o' {
            // Count vv pairs after this position
            var vvAfter := 0;
            
            if pos + 1 < |s| - 1 {
                var j := pos + 1;
                
                while j < |s| - 1
                    invariant pos + 1 <= j <= |s| - 1
                    invariant vvAfter >= 0
                    invariant vvAfter == countVVPairsAfter(s, pos + 1) - countVVPairsAfter(s, j)
                {
                    if s[j] == 'v' && s[j + 1] == 'v' {
                        vvAfter := vvAfter + 1;
                    }
                    j := j + 1;
                }
            }
            
            assert vvAfter == countVVPairsAfter(s, pos + 1);
            sum := sum + vvBefore * vvAfter;
        }
        
        // Update vvBefore for next iteration
        if pos > 0 && s[pos - 1] == 'v' && s[pos] == 'v' {
            vvBefore := vvBefore + 1;
        }
        
        pos := pos + 1;
    }
    
    assert sum == wowFactorSum(s, 0);
    result := sum;
}
// </vc-code>

