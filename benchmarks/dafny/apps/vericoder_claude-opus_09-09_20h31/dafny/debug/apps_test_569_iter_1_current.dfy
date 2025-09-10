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
        assert set c | c in s == {};
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
        var distinctCount := CountDistinctChars(s);
        SetSizeUpperBound(s);
        assert distinctCount <= |s|;
        assert distinctCount <= n;
        result := n - distinctCount;
        assert result == |s| - distinctCount;
        return result;
    }
}
// </vc-code>

