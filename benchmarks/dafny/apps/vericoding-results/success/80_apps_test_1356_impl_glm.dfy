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
lemma CountAtLeastOne(s: string)
    requires ValidInput(s)
    ensures count_a(s) >= 1
    decreases |s|
{
    if |s| == 0 {
        assert false;
    } else if s[0] == 'a' {
        // count_a(s) = 1 + count_a(s[1..]) >= 1
    } else {
        assert |s| >= 2;
        assert ValidInput(s[1..]);
        CountAtLeastOne(s[1..]);
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
    var c := count_a(s);
    CountAtLeastOne(s);
    if 2 * c - 1 <= n {
        result := 2 * c - 1;
    } else {
        result := n;
    }
}
// </vc-code>

