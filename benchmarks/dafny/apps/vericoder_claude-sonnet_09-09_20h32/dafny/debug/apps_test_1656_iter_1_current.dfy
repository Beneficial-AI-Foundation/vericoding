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
        result := 0;
    } else {
        result := 0;
        var pos := 0;
        
        while pos < |s|
            invariant 0 <= pos <= |s|
            invariant result == wowFactorSum(s, 0) - wowFactorSum(s, pos)
            invariant result >= 0
        {
            if s[pos] == 'o' {
                var vvBefore := 0;
                var i := 1;
                while i < pos
                    invariant 1 <= i <= pos
                    invariant vvBefore == countVVPairsBefore(s, i)
                {
                    if s[i] == 'v' && s[i-1] == 'v' {
                        vvBefore := vvBefore + 1;
                    }
                    i := i + 1;
                }
                
                var vvAfter := 0;
                var j := pos + 1;
                while j < |s| - 1
                    invariant pos + 1 <= j <= |s| - 1
                    invariant vvAfter == countVVPairsAfter(s, pos + 1) - countVVPairsAfter(s, j)
                {
                    if s[j] == 'v' && s[j+1] == 'v' {
                        vvAfter := vvAfter + 1;
                    }
                    j := j + 1;
                }
                
                result := result + vvBefore * vvAfter;
            }
            pos := pos + 1;
        }
    }
}
// </vc-code>

