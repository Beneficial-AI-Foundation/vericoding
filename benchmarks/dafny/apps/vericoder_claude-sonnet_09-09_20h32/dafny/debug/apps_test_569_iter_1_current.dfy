predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
lemma CountDistinctCharsAtMost26(s: string)
    ensures CountDistinctChars(s) <= 26
{
    var chars := set c | c in s;
    assert chars <= set c: char | true;
}

lemma CountDistinctCharsAtMostLength(s: string)
    ensures CountDistinctChars(s) <= |s|
{
    var chars := set c | c in s;
    assert |chars| <= |s|;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures n > 26 ==> result == -1
    ensures n <= 26 ==> result >= 0 && result < n
    ensures n <= 26 ==> result == |s| - CountDistinctChars(s)
// </vc-spec>
// <vc-code>
{
    if n > 26 {
        result := -1;
    } else {
        var distinctChars := CountDistinctChars(s);
        result := n - distinctChars;
        CountDistinctCharsAtMost26(s);
        CountDistinctCharsAtMostLength(s);
    }
}
// </vc-code>

