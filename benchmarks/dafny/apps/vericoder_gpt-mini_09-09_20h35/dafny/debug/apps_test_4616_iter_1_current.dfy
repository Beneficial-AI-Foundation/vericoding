predicate ValidInput(s: string)
{
    |s| >= 3 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidAbbreviation(s: string, result: string)
{
    |result| >= 3 &&
    |s| >= 3 &&
    result[0] == s[0] &&
    result[|result|-1] == s[|s|-1] &&
    result == [s[0]] + IntToString(|s| - 2) + [s[|s|-1]]
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char]
}

// <vc-helpers>
lemma IntToStringHelper_nonempty(n: int)
    requires n >= 1
    ensures |IntToStringHelper(n)| >= 1
    decreases n
{
    if n / 10 == 0 {
        // n in 1..9
        assert IntToStringHelper(n) == IntToStringHelper(0) + [(('0' as int) + (n % 10)) as char];
        assert IntToStringHelper(0) == "";
        assert |IntToStringHelper(n)| == 1;
    } else {
        // n/10 >= 1 and n/10 < n
        IntToStringHelper_nonempty(n / 10);
        assert IntToStringHelper(n) == IntToStringHelper(n / 10) + [(('0' as int) + (n % 10)) as char];
        assert |IntToStringHelper(n)| == |IntToStringHelper(n / 10)| + 1;
        assert |IntToStringHelper(n)| >= 1;
    }
}

lemma IntToString_nonempty(n: int)
    requires n >= 1
    ensures |IntToString(n)| >= 1
{
    // For n >= 1, IntToString(n) == IntToStringHelper(n)
    assert IntToString(n) == IntToStringHelper(n);
    IntToStringHelper_nonempty(n);
    assert |IntToString(n)| == |IntToStringHelper(n)|;
    assert |IntToString(n)| >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidAbbreviation(s, result)
// </vc-spec>
// <vc-code>
{
    IntToString_nonempty(|s| - 2);
    result := [s[0]] + IntToString(|s| - 2) + [s[|s|-1]];
}
// </vc-code>

