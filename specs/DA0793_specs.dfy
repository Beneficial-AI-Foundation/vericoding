// <vc-preamble>
predicate ValidInput(n: int)
{
    n >= 2 && n <= 100000
}

function SectionsForDigit(d: char): int
{
    match d
        case '0' => 6
        case '1' => 2
        case '2' => 5
        case '3' => 5
        case '4' => 4
        case '5' => 5
        case '6' => 6
        case '7' => 3
        case '8' => 7
        case '9' => 6
        case _ => 0
}

function TotalSections(s: string): int
{
    if |s| == 0 then 0
    else SectionsForDigit(s[0]) + TotalSections(s[1..])
}

predicate ValidDigitString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
}

predicate OptimalResult(result: string, n: int)
{
    ValidDigitString(result) &&
    TotalSections(result) <= n &&
    (forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '7') &&
    (n % 2 != 0 ==> result[0] == '7' && |result| == 1 + (n - 3) / 2) &&
    (n % 2 == 0 ==> result[0] == '1' && |result| == 1 + (n - 2) / 2) &&
    (n % 2 != 0 ==> (forall i :: 1 <= i < |result| ==> result[i] == '1')) &&
    (n % 2 == 0 ==> (forall i :: 1 <= i < |result| ==> result[i] == '1')) &&
    (n % 2 != 0 ==> 3 + 2 * (|result| - 1) == n) &&
    (n % 2 == 0 ==> 2 * |result| == n)
}
// </vc-preamble>

// <vc-helpers>
lemma TotalSectionsAdditive(s1: string, s2: string)
    ensures TotalSections(s1 + s2) == TotalSections(s1) + TotalSections(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        TotalSectionsAdditive(s1[1..], s2);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures OptimalResult(result, n)
// </vc-spec>
// <vc-code>
{
    var remaining := n;
    var s := "";

    if remaining % 2 != 0 {
        s := "7";
        remaining := remaining - 3;
    } else {
        s := "1";
        remaining := remaining - 2;
    }

    var count := remaining / 2;
    var i := 0;
    while i < count
        invariant 0 <= i <= count
        invariant |s| == 1 + i
        invariant n % 2 != 0 ==> s[0] == '7'
        invariant n % 2 == 0 ==> s[0] == '1'
        invariant forall j :: 0 <= j < |s| ==> s[j] == '1' || s[j] == '7'
        invariant forall j :: 1 <= j < |s| ==> s[j] == '1'
        invariant n % 2 != 0 ==> count == (n - 3) / 2
        invariant n % 2 == 0 ==> count == (n - 2) / 2
        invariant n % 2 != 0 ==> TotalSections(s) == 3 + 2 * i
        invariant n % 2 == 0 ==> TotalSections(s) == 2 + 2 * i
        invariant n % 2 != 0 ==> remaining == n - 3 && remaining % 2 == 0
        invariant n % 2 == 0 ==> remaining == n - 2 && remaining % 2 == 0
    {
        TotalSectionsAdditive(s, "1");
        s := s + "1";
        i := i + 1;
    }

    result := s;
}
// </vc-code>
