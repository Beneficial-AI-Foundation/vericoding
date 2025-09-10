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
lemma MinLowerBound(a: int, b: int, lower: int)
    requires a >= lower
    requires b >= lower
    ensures min(a, b) >= lower
{
}

lemma CountAAtLeastOne(s: string)
    requires ValidInput(s)
    ensures count_a(s) >= 1
{
    assert exists i :: 0 <= i < |s| && s[i] == 'a';
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
    var count := count_a(s);
    CountAAtLeastOne(s);
    result := min(2 * count - 1, |s|);
    MinLowerBound(2 * count - 1, |s|, 1);
}
// </vc-code>

