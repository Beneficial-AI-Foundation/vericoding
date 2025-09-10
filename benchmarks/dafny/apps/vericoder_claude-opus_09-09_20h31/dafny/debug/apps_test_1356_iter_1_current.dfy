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
lemma CountAPositive(s: string)
    requires ValidInput(s)
    ensures count_a(s) >= 1
{
    // ValidInput ensures there exists an 'a' in the string
    var i :| 0 <= i < |s| && s[i] == 'a';
    CountAContainsIndex(s, i);
}

lemma CountAContainsIndex(s: string, i: int)
    requires 0 <= i < |s|
    requires s[i] == 'a'
    ensures count_a(s) >= 1
    decreases |s|
{
    if i == 0 {
        // s[0] == 'a', so count_a(s) = 1 + count_a(s[1..]) >= 1
        assert count_a(s) == 1 + count_a(s[1..]);
    } else {
        // i > 0, so we need to look in s[1..]
        assert s[1..][i-1] == s[i] == 'a';
        if |s| > 1 {
            CountAContainsIndex(s[1..], i-1);
            assert count_a(s[1..]) >= 1;
        }
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
    var count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == count_a(s[..i])
    {
        if s[i] == 'a' {
            count := count + 1;
        }
        i := i + 1;
    }
    
    assert s[..|s|] == s;
    assert count == count_a(s);
    
    CountAPositive(s);
    assert count >= 1;
    
    var twice_minus_one := 2 * count - 1;
    assert twice_minus_one == 2 * count_a(s) - 1;
    
    if twice_minus_one <= |s| {
        result := twice_minus_one;
    } else {
        result := |s|;
    }
    
    assert result == min(2 * count_a(s) - 1, |s|);
}
// </vc-code>

