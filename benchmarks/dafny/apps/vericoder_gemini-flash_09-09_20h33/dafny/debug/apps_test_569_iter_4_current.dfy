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
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall c: char :: c in counts.Keys <==> (exists k: int :: 0 <= k < i && s[k] == c)
        invariant forall c: char :: c in counts.Keys ==> counts[c] == (Ghost_CountOccurrences(s, c, i))
    {
        var c := s[i];
        if c in counts {
            counts := counts[c := counts[c] + 1];
        } else {
            counts := counts[c := 1];
        }
        i := i + 1;
    }
    return counts;
}

// Helper function to count occurrences of a character in a prefix of a string
// Used in the invariant of GetCharCounts
function Ghost_CountOccurrences(s: string, c: char, limit: int): int
    requires 0 <= limit <= |s|
{
    var count := 0;
    for k := 0 to limit - 1
        invariant 0 <= k <= limit
        invariant count == (forall i: int :: 0 <= i < k && s[i] == c : 1) as int
    {
        if s[k] == c {
            count := count + 1;
        }
    }
    return count;
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

