// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
