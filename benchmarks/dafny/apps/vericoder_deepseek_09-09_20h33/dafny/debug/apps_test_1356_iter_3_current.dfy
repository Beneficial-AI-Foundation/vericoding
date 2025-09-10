function count_a(s: string): int
    ensures count_a(s) >= 0
    ensures count_a(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'a' then 1 else 0) + count_a(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidInput(s: string)
{
    |s| >= 1 && exists i :: 0 <= i < |s| && s[i] == 'a'
}

predicate IsGoodString(s: string)
{
    |s| > 0 && count_a(s) > |s| / 2
}

// <vc-helpers>
lemma count_a_slice(s: string, i: int)
    requires 0 <= i <= |s|
    ensures count_a(s[i:]) >= 0
    decreases |s| - i
{
    if i < |s| {
        count_a_slice(s, i + 1);
    }
}

lemma count_a_nonnegative(s: string)
    ensures count_a(s) >= 0
{
    count_a_slice(s, 0);
}

lemma count_a_monotonic(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures count_a(s[i:]) >= count_a(s[j:])
    decreases j - i
{
    if i < j {
        count_a_monotonic(s, i + 1, j);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 1
    ensures result <= |s|
    ensures result == min(2 * count_a(s) - 1, |s|)
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    var a_count := count_a(s);
    var candidate := 2 * a_count - 1;
    
    if candidate <= n {
        result := candidate;
    } else {
        result := n;
    }
}
// </vc-code>

