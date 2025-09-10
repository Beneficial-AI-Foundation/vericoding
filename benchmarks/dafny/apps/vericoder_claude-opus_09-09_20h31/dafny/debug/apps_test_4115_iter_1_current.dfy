predicate ValidInput(s: string)
{
    |s| >= 1
}

function count_mismatches_up_to(s: string, limit: int): int
    requires |s| >= 1
    requires 0 <= limit <= |s|
    ensures count_mismatches_up_to(s, limit) >= 0
    ensures count_mismatches_up_to(s, limit) <= limit
{
    if limit == 0 then 0
    else 
        var n := |s| - 1;
        var mismatch := if s[limit-1] != s[n - (limit-1)] then 1 else 0;
        count_mismatches_up_to(s, limit-1) + mismatch
}

function count_mismatches(s: string): int
    requires |s| >= 1
    ensures count_mismatches(s) >= 0
{
    count_mismatches_up_to(s, |s|)
}

predicate ValidResult(s: string, result: int)
    requires ValidInput(s)
{
    result >= 0 && result <= |s| / 2 && result == (count_mismatches(s) / 2)
}

// <vc-helpers>
lemma count_mismatches_up_to_increment(s: string, i: int)
    requires |s| >= 1
    requires 0 <= i < |s|
    ensures count_mismatches_up_to(s, i + 1) == 
            count_mismatches_up_to(s, i) + (if s[i] != s[|s| - 1 - i] then 1 else 0)
{
    // This follows directly from the definition of count_mismatches_up_to
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures ValidResult(s, result)
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    var count := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant count == count_mismatches_up_to(s, i)
    {
        if s[i] != s[n - 1 - i] {
            count := count + 1;
        }
        count_mismatches_up_to_increment(s, i);
        i := i + 1;
    }
    
    assert i == n;
    assert count == count_mismatches_up_to(s, n);
    assert count == count_mismatches(s);
    
    result := count / 2;
}
// </vc-code>

