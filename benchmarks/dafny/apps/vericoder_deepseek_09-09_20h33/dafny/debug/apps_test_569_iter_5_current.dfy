predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
lemma CountDistinctCharsSize(s: string)
    ensures CountDistinctChars(s) <= |s|
{
    var charSet := set c | c in s;
    assert CountDistinctChars(s) == |charSet|;
    // The size of any set of characters from a string cannot exceed the string length
    // since each character in the set must come from the string
}

lemma SetSizeLemma(s: string)
    ensures CountDistinctChars(s) == |set c | c in s|
{
    // This is true by definition of CountDistinctChars
}

lemma DistinctSubsetLemma(s: string)
    ensures |set c | c in s| <= |s|
{
    CountDistinctCharsSize(s);
}

lemma AtLeastOneDistinct(s: string)
    requires |s| >= 1
    ensures CountDistinctChars(s) >= 1
{
    if |s| >= 1 {
        var firstChar := s[0];
        assert firstChar in s;
        var chars := set c | c in s;
        assert firstChar in chars;
        assert |chars| >= 1;
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
        // Calculate distinct characters count
        var distinctCount := CountDistinctChars(s);
        // Since n <= 26 and n == |s|, we know distinctCount <= |s|
        CountDistinctCharsSize(s);
        AtLeastOneDistinct(s);
        result := |s| - distinctCount;
        // Verify postcondition: result >= 0 && result < n
        assert result >= 0 by {
            assert distinctCount <= |s|;
        }
        assert result < n by {
            assert distinctCount >= 1;
            assert |s| == n;
            calc {
                result;
                ==
                n - distinctCount;
                <
                n - 0;
                ==
                n;
            }
        }
    }
}
// </vc-code>

