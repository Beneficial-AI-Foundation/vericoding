Given a string s of n lowercase Latin letters, find the minimum number of operations
to construct it starting from an empty string. Operations are: (1) add one character
to the end (unlimited use), (2) copy current string and append it to itself (at most once).

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

method solve(n: nat, s: string) returns (result: nat)
    requires ValidInput(n, s)
    ensures result <= n
    ensures n == 0 ==> result == 0
    ensures n > 0 ==> result >= 1
    ensures result == n - MaxCopySavings(s, n)
{
    var ans := n;
    var ma := 0;

    var i := 0;
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant 0 <= ma <= i
        invariant ma == MaxCopySavingsUpTo(s, n, i)
    {
        // Build prefix s[0..i] (i+1 characters)
        var prefix := s[0..i+1];

        // Check if we can copy at this position
        // We need to compare s[i+1..2*i+1] with the prefix
        var end_pos := i + 1 + (i + 1);  // i + 1 + length of prefix

        if end_pos <= n {
            var suffix := s[i+1..end_pos];
            if suffix == prefix {
                ma := i;
            }
        }

        i := i + 1;
    }

    result := ans - ma;
}
