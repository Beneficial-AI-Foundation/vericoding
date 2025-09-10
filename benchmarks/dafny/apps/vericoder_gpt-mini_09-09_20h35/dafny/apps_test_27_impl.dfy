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
lemma MaxCopySavings_le_n(s: string, n: nat)
    requires |s| == n
    ensures MaxCopySavings(s, n) <= n
{
    // From the contract of MaxCopySavings we know it is <= n/2, and n/2 <= n.
    assert MaxCopySavings(s, n) <= n / 2;
    assert n / 2 <= n;
}

lemma NatHalfDifferenceAtLeastOne(n: nat)
    requires n > 0
    ensures n - n / 2 >= 1
{
    if n == 1 {
        // 1 - 1/2 = 1 - 0 = 1
        assert n - n / 2 == 1;
    } else {
        // n >= 2, so n/2 <= n-1, hence n - n/2 >= 1
        assert n / 2 <= n - 1;
        assert n - n / 2 >= 1;
    }
}
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
    var m := MaxCopySavings(s, n);
    // Ensure m <= n so subtraction yields a nat
    MaxCopySavings_le_n(s, n);
    result := n - m;

    // Prove the postconditions
    if n == 0 {
        // n == 0 implies m == 0, so result == 0
        assert m <= 0;
        assert m == 0;
        assert result == 0;
    } else {
        // n > 0 implies result >= 1
        assert m <= n / 2;
        NatHalfDifferenceAtLeastOne(n);
        assert result >= n - n / 2;
        assert result >= 1;
    }

    // result <= n follows since m >= 0
    assert result <= n;
}
// </vc-code>

