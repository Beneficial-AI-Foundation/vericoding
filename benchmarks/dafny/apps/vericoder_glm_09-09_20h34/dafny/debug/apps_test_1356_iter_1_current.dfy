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
    var a_count := 0;
    var i := 0;
    while i < |s|
    invariant 0 <= i <= |s|
    invariant a_count == count_a(s[0..i])
    {
        if s[i] == 'a' {
            a_count := a_count + 1;
        }
        i := i + 1;
    }
    result := min(2 * a_count - 1, |s|);
}
// </vc-code>

