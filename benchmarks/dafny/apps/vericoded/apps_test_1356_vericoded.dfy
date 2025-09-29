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

lemma CountAExtend(s: string, i: int)
    requires 0 <= i < |s|
    ensures count_a(s[..i+1]) == count_a(s[..i]) + (if s[i] == 'a' then 1 else 0)
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert s[..0] == [];
        assert count_a([]) == 0;
        assert count_a([s[0]]) == (if s[0] == 'a' then 1 else 0);
    } else {
        // For i > 0, we need to relate s[..i+1] to s[..i]
        // s[..i+1] = s[..i] + [s[i]]
        assert s[..i+1][0] == s[0];
        assert s[..i+1][1..] == s[1..][..i];
        
        // By definition of count_a:
        // count_a(s[..i+1]) = (if s[0] == 'a' then 1 else 0) + count_a(s[..i+1][1..])
        // count_a(s[..i]) = (if s[0] == 'a' then 1 else 0) + count_a(s[..i][1..])
        
        assert s[..i][1..] == s[1..][..i-1];
        assert s[..i+1][1..] == s[1..][..i];
        
        // Recursively apply to the suffix
        CountAExtend(s[1..], i-1);
        
        // This gives us: count_a(s[1..][..i]) == count_a(s[1..][..i-1]) + (if s[1..][i-1] == 'a' then 1 else 0)
        assert s[1..][i-1] == s[i];
        assert count_a(s[1..][..i]) == count_a(s[1..][..i-1]) + (if s[i] == 'a' then 1 else 0);
        
        // Now we can conclude:
        assert count_a(s[..i+1]) == (if s[0] == 'a' then 1 else 0) + count_a(s[1..][..i]);
        assert count_a(s[..i]) == (if s[0] == 'a' then 1 else 0) + count_a(s[1..][..i-1]);
        assert count_a(s[..i+1]) == count_a(s[..i]) + (if s[i] == 'a' then 1 else 0);
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
        CountAExtend(s, i);
        if s[i] == 'a' {
            count := count + 1;
        }
        assert count == count_a(s[..i]) + (if s[i] == 'a' then 1 else 0);
        assert count == count_a(s[..i+1]);
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

