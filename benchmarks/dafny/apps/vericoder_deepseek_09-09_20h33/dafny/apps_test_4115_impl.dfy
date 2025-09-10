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
lemma MismatchLemma(s: string, limit: int)
    requires |s| >= 1
    requires 0 <= limit <= |s|
    ensures count_mismatches_up_to(s, limit) == count_mismatches_up_to(s, limit) / 2 * 2 + (count_mismatches_up_to(s, limit) % 2)
    decreases limit
{
    if limit > 0 {
        MismatchLemma(s, limit - 1);
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
    var n := |s|;
    var total_mismatches := count_mismatches(s);
    result := total_mismatches / 2;
}
// </vc-code>

