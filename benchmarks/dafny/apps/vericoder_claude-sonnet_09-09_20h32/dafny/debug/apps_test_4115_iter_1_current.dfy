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
lemma count_mismatches_up_to_step(s: string, limit: int)
    requires |s| >= 1
    requires 1 <= limit <= |s|
    ensures count_mismatches_up_to(s, limit) == count_mismatches_up_to(s, limit-1) + 
            (if s[limit-1] != s[|s| - 1 - (limit-1)] then 1 else 0)
{
}

lemma count_mismatches_iterative_correct(s: string, count: int, i: int)
    requires |s| >= 1
    requires 0 <= i <= |s|
    requires count == count_mismatches_up_to(s, i)
    ensures count + count_mismatches_up_to_from(s, i, |s|) == count_mismatches(s)
{
    if i == |s| {
        assert count_mismatches_up_to_from(s, i, |s|) == 0;
    } else {
        count_mismatches_iterative_correct(s, count + (if s[i] != s[|s| - 1 - i] then 1 else 0), i + 1);
    }
}

function count_mismatches_up_to_from(s: string, start: int, limit: int): int
    requires |s| >= 1
    requires 0 <= start <= limit <= |s|
    ensures count_mismatches_up_to_from(s, start, limit) >= 0
{
    if start >= limit then 0
    else 
        var mismatch := if s[start] != s[|s| - 1 - start] then 1 else 0;
        mismatch + count_mismatches_up_to_from(s, start + 1, limit)
}

lemma count_mismatches_split(s: string, mid: int)
    requires |s| >= 1
    requires 0 <= mid <= |s|
    ensures count_mismatches_up_to(s, |s|) == count_mismatches_up_to(s, mid) + count_mismatches_up_to_from(s, mid, |s|)
{
    if mid == 0 {
        assert count_mismatches_up_to(s, 0) == 0;
        count_mismatches_up_to_from_equals_up_to(s, 0, |s|);
    } else if mid == |s| {
        assert count_mismatches_up_to_from(s, |s|, |s|) == 0;
    } else {
        count_mismatches_split(s, mid + 1);
    }
}

lemma count_mismatches_up_to_from_equals_up_to(s: string, start: int, limit: int)
    requires |s| >= 1
    requires start == 0
    requires 0 <= start <= limit <= |s|
    ensures count_mismatches_up_to_from(s, start, limit) == count_mismatches_up_to(s, limit)
{
    if limit == 0 {
    } else {
        count_mismatches_up_to_from_equals_up_to(s, 0, limit - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures ValidResult(s, result)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    var n := |s|;
    
    while i < n
        invariant 0 <= i <= n
        invariant count == count_mismatches_up_to(s, i)
        invariant count >= 0
    {
        if s[i] != s[n - 1 - i] {
            count := count + 1;
        }
        count_mismatches_up_to_step(s, i + 1);
        i := i + 1;
    }
    
    assert count == count_mismatches_up_to(s, |s|);
    assert count == count_mismatches(s);
    
    result := count / 2;
}
// </vc-code>

