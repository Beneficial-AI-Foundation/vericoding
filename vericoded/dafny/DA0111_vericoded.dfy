predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
lemma SetSizeUpperBound(s: string)
    ensures |set c | c in s| <= |s|
{
    if |s| == 0 {
        assert s == "";
        var emptySet: set<char> := {};
        assert (set c | c in s) == emptySet;
    } else {
        var s' := s[..|s|-1];
        var lastChar := s[|s|-1];
        SetSizeUpperBound(s');
        
        var setS' := set c | c in s';
        var setS := set c | c in s;
        
        assert setS == setS' + {lastChar} || setS == setS';
        
        if lastChar in setS' {
            assert setS == setS';
        } else {
            assert setS == setS' + {lastChar};
            assert |setS| == |setS'| + 1;
        }
    }
}

lemma NonEmptyStringHasDistinctChars(s: string)
    requires |s| >= 1
    ensures CountDistinctChars(s) >= 1
{
    assert s[0] in s;
    var charSet := set c | c in s;
    assert s[0] in charSet;
    assert |charSet| >= 1;
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
        return -1;
    } else {
        SetSizeUpperBound(s);
        NonEmptyStringHasDistinctChars(s);
        var distinctCount := CountDistinctChars(s);
        assert distinctCount >= 1;
        assert distinctCount <= |s|;
        assert distinctCount <= n;
        result := n - distinctCount;
        assert result >= 0;
        assert result < n;
        assert result == |s| - distinctCount;
        return result;
    }
}
// </vc-code>

