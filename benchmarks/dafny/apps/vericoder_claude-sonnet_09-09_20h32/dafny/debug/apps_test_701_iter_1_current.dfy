function ParseLines(stdin_input: string): seq<string>
    decreases |stdin_input|
{
    if |stdin_input| == 0 then []
    else
        var newline_pos := FindNewline(stdin_input, 0);
        if newline_pos == -1 then [stdin_input]
        else if newline_pos == 0 then ParseLines(stdin_input[1..])
        else if newline_pos < |stdin_input| && newline_pos >= 0
        then [stdin_input[..newline_pos]] + ParseLines(stdin_input[newline_pos+1..])
        else []
}

function FindNewline(s: string, start: int): int
    requires 0 <= start
    decreases |s| - start
    ensures FindNewline(s, start) == -1 || (start <= FindNewline(s, start) < |s|)
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

predicate ValidInput(stdin_input: string)
{
    var lines := ParseLines(stdin_input);
    |lines| >= 2 && |lines[0]| > 0 && |lines[1]| > 0 &&
    (forall c :: c in lines[0] ==> 'a' <= c <= 'z') &&
    (forall c :: c in lines[1] ==> 'a' <= c <= 'z')
}

function IsSubsequence(s: string, t: string): bool
{
    if |s| == 0 then true
    else if |t| == 0 then false
    else if s[0] == t[0] then IsSubsequence(s[1..], t[1..])
    else IsSubsequence(s, t[1..])
}

function SortString(s: string): string
    decreases |s|
{
    if |s| <= 1 then s
    else 
        var pivot := s[0];
        var smaller := FilterChars(s[1..], pivot, true, false);
        var equal := FilterChars(s, pivot, false, true);
        var larger := FilterChars(s[1..], pivot, false, false);
        SortString(smaller) + equal + SortString(larger)
}

function FilterChars(s: string, pivot: char, takeLess: bool, takeEqual: bool): string
    decreases |s|
    ensures |FilterChars(s, pivot, takeLess, takeEqual)| <= |s|
{
    if |s| == 0 then ""
    else 
        var first := s[0];
        var rest := FilterChars(s[1..], pivot, takeLess, takeEqual);
        if (takeLess && first < pivot) || (takeEqual && first == pivot) || (!takeLess && !takeEqual && first > pivot)
        then [first] + rest
        else rest
}

// <vc-helpers>
lemma SortStringPreservesChars(s: string)
    ensures multiset(s) == multiset(SortString(s))
    decreases |s|
{
    if |s| <= 1 {
        // Base case is trivial
    } else {
        var pivot := s[0];
        var smaller := FilterChars(s[1..], pivot, true, false);
        var equal := FilterChars(s, pivot, false, true);
        var larger := FilterChars(s[1..], pivot, false, false);
        
        FilterCharsPreservesMultiset(s[1..], pivot, true, false);
        FilterCharsPreservesMultiset(s, pivot, false, true);
        FilterCharsPreservesMultiset(s[1..], pivot, false, false);
        
        SortStringPreservesChars(smaller);
        SortStringPreservesChars(larger);
    }
}

lemma FilterCharsPreservesMultiset(s: string, pivot: char, takeLess: bool, takeEqual: bool)
    ensures multiset(FilterChars(s, pivot, takeLess, takeEqual)) <= multiset(s)
    decreases |s|
{
    if |s| == 0 {
        // Base case
    } else {
        FilterCharsPreservesMultiset(s[1..], pivot, takeLess, takeEqual);
    }
}

lemma SortStringEquality(s: string, t: string)
    requires SortString(s) == SortString(t)
    ensures multiset(s) == multiset(t)
{
    SortStringPreservesChars(s);
    SortStringPreservesChars(t);
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures result in ["array", "automaton", "both", "need tree"]
    ensures var lines := ParseLines(stdin_input);
            var s := lines[0];
            var t := lines[1];
            var sx := SortString(s);
            var tx := SortString(t);
            ((sx == tx && result == "array") ||
             (sx != tx && IsSubsequence(t, s) && result == "automaton") ||
             (sx != tx && !IsSubsequence(t, s) && IsSubsequence(tx, sx) && result == "both") ||
             (sx != tx && !IsSubsequence(t, s) && !IsSubsequence(tx, sx) && result == "need tree"))
// </vc-spec>
// <vc-code>
{
    var lines := ParseLines(stdin_input);
    var s := lines[0];
    var t := lines[1];
    var sx := SortString(s);
    var tx := SortString(t);
    
    if sx == tx {
        result := "array";
    } else if IsSubsequence(t, s) {
        result := "automaton";
    } else if IsSubsequence(tx, sx) {
        result := "both";
    } else {
        result := "need tree";
    }
}
// </vc-code>

