Given a string of lowercase English letters, find the minimum number of character 
changes needed to make all substrings distinct. If the string length exceeds 26,
it's impossible since we only have 26 distinct lowercase letters available.

predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures n > 26 ==> result == -1
    ensures n <= 26 ==> result >= 0 && result < n
    ensures n <= 26 ==> result == |s| - CountDistinctChars(s)
{
    if n > 26 {
        result := -1;
        return;
    }

    // Count character frequencies
    var frequencies := map[];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall c :: c in frequencies <==> c in s[..i]
        invariant forall c :: c in frequencies ==> frequencies[c] >= 1
        invariant i > 0 ==> |frequencies| >= 1
        invariant |frequencies| <= i
    {
        var c := s[i];
        if c in frequencies {
            frequencies := frequencies[c := frequencies[c] + 1];
        } else {
            frequencies := frequencies[c := 1];
        }
        i := i + 1;
    }

    assert forall c :: c in frequencies <==> c in s;
    assert frequencies.Keys == set c | c in s;
    assert |frequencies| == |set c | c in s|;
    assert |s| >= 1;
    assert |frequencies| >= 1;
    assert |frequencies| <= |s|;

    result := |s| - |frequencies|;
    assert result >= 0;
    assert result == |s| - |frequencies| < |s|;
}
