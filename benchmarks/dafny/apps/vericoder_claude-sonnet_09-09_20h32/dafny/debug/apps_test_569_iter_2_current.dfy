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
    assert chars <= set c: char {:trigger} | true;
    assert |chars| <= 26;
}

lemma CountDistinctCharsAtMostLength(s: string)
    ensures CountDistinctChars(s) <= |s|
{
    var chars := set c | c in s;
    if |s| == 0 {
        assert chars == {};
        assert |chars| == 0;
    } else {
        assert forall c :: c in chars ==> c in s;
        CardinalitySubset(chars, s);
    }
}

lemma CardinalitySubset(chars: set<char>, s: string)
    requires forall c :: c in chars ==> c in s
    ensures |chars| <= |s|
{
    if |s| == 0 {
        assert chars == {};
    } else if |chars| == 0 {
        assert |chars| <= |s|;
    } else {
        var char_seq := seq(|s|, i => s[i]);
        assert set c | c in char_seq == set c | c in s;
        assert |set c | c in char_seq| <= |char_seq|;
        assert |char_seq| == |s|;
    }
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
        CountDistinctCharsAtMost26(s);
        CountDistinctCharsAtMostLength(s);
        var distinctChars := CountDistinctChars(s);
        result := n - distinctChars;
        assert distinctChars <= 26;
        assert distinctChars <= |s|;
        assert n == |s|;
        assert result == |s| - distinctChars;
        assert result >= 0;
        assert result < n;
    }
}
// </vc-code>

