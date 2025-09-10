predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
function GetCharCounts(s: string): map<char, int>
{
    var counts := map[];
    for i := 0 to |s| - 1
    {
        var c := s[i];
        if c in counts {
            counts := counts[c := counts[c] + 1];
        } else {
            counts := counts[c := 1];
        }
    }
    return counts;
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
    }

    var counts := GetCharCounts(s);
    var duplicates := 0;
    for c in counts.Keys {
        if counts[c] > 1 {
            duplicates := duplicates + (counts[c] - 1);
        }
    }
    return duplicates;
}
// </vc-code>

