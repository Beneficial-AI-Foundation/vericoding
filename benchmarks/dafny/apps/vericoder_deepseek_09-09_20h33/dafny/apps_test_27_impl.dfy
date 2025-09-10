predicate ValidInput(n: nat, s: string)
{
    |s| == n
}

function MaxCopySavings(s: string, n: nat): nat
    requires |s| == n
    ensures MaxCopySavings(s, n) <= n / 2
{
    MaxCopySavingsUpTo(s, n, n / 2)
}

function MaxCopySavingsUpTo(s: string, n: nat, limit: nat): nat
    requires |s| == n
    requires limit <= n / 2
    ensures MaxCopySavingsUpTo(s, n, limit) <= limit
    decreases limit
{
    if limit == 0 then 0
    else
        var i := limit - 1;
        var current := if CanCopyAt(s, n, i) then i else 0;
        var prev := MaxCopySavingsUpTo(s, n, i);
        if current > prev then current else prev
}

predicate CanCopyAt(s: string, n: nat, i: nat)
    requires |s| == n
    requires i < n / 2
{
    var prefix_len := i + 1;
    var end_pos := i + 1 + prefix_len;
    end_pos <= n && s[0..prefix_len] == s[i+1..end_pos]
}

// <vc-helpers>
lemma MaxCopySavingsUpToMonotonic(s: string, n: nat, limit1: nat, limit2: nat)
    requires |s| == n
    requires limit1 <= limit2 <= n / 2
    ensures MaxCopySavingsUpTo(s, n, limit1) <= MaxCopySavingsUpTo(s, n, limit2)
    decreases limit2 - limit1
{
    if limit1 == limit2 {
    } else {
        MaxCopySavingsUpToMonotonic(s, n, limit1, limit2 - 1);
    }
}

lemma MaxCopySavingsUpToCorrect(s: string, n: nat, limit: nat)
    requires |s| == n
    requires limit <= n / 2
    ensures MaxCopySavingsUpTo(s, n, limit) == 0 || CanCopyAt(s, n, MaxCopySavingsUpTo(s, n, limit) - 1)
{
    if limit == 0 {
    } else {
        var i := limit - 1;
        var current := if CanCopyAt(s, n, i) then i else 0;
        var prev := MaxCopySavingsUpTo(s, n, i);
        
        MaxCopySavingsUpToCorrect(s, n, i);
        
        if current > prev {
            if current > 0 {
                assert CanCopyAt(s, n, current - 1) by {
                    assert current == i;
                }
            }
        } else {
            if prev > 0 {
                assert CanCopyAt(s, n, prev - 1);
            }
        }
    }
}

lemma MaxCopySavingsCorrect(s: string, n: nat)
    requires |s| == n
    ensures MaxCopySavings(s, n) == 0 || CanCopyAt(s, n, MaxCopySavings(s, n) - 1)
{
    var limit := n / 2;
    MaxCopySavingsUpToCorrect(s, n, limit);
}

lemma SavingsBounds(n: nat, savings: nat)
    requires savings <= n / 2
    ensures n - savings >= 1 when n > 0
{
    if n > 0 {
        assert n - savings >= n - (n / 2);
        var half := n / 2;
        if n % 2 == 0 {
            assert half == n / 2;
        } else {
            assert half == (n - 1) / 2;
        }
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: nat, s: string) returns (result: nat)
    requires ValidInput(n, s)
    ensures result <= n
    ensures n == 0 ==> result == 0
    ensures n > 0 ==> result >= 1
    ensures result == n - MaxCopySavings(s, n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        result := 0;
        return;
    }
    
    var savings: nat := MaxCopySavings(s, n);
    result := n - savings;
    
    assert result >= 1 && result <= n by {
        SavingsBounds(n, savings);
        assert result == n - savings;
        assert n - savings <= n;
    }
    
    MaxCopySavingsCorrect(s, n);
}
// </vc-code>

