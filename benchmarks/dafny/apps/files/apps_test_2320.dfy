Given two strings s and t of equal length, determine the minimum number of moves needed to transform s into t.
In each move, you can select any character from s and move it to either the beginning or end of the string.
If transformation is impossible, return -1.

function CountCharacter(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountCharacter(s[1..], c)
}

function HasSameCharacterCounts(s: string, t: string): bool
{
    |s| == |t| && 
    (forall c :: CountCharacter(s, c) == CountCharacter(t, c))
}

function FindNextMatch(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNextMatch(s, c, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == c then start
    else FindNextMatch(s, c, start + 1)
}

function CanMatchSubstring(s: string, t: string, i: int, j: int, k: int): bool
    requires 0 <= i <= j < |t|
    requires 0 <= k <= |s|
    requires |s| == |t|
    decreases j - i + 1, |s| - k
{
    if i > j then true
    else if k >= |s| then false
    else 
        var nextK := FindNextMatch(s, t[j], k);
        if nextK >= |s| then false
        else if i == j then true
        else 
            assert nextK < |s|;
            CanMatchSubstring(s, t, i, j-1, nextK+1)
}

function MaxPreservableLength(s: string, t: string, i: int, j: int, maxSoFar: int): int
    requires 0 <= i <= |t|
    requires i <= j <= |t|
    requires |s| == |t|
    requires maxSoFar >= 0
    requires maxSoFar <= |s|
    ensures MaxPreservableLength(s, t, i, j, maxSoFar) >= maxSoFar
    ensures MaxPreservableLength(s, t, i, j, maxSoFar) <= |s|
    decreases |t| - i, |t| - j
{
    if i >= |t| then maxSoFar
    else if j >= |t| then MaxPreservableLength(s, t, i+1, i+1, maxSoFar)
    else 
        var currentLen := j - i + 1;
        var canMatch := CanMatchSubstring(s, t, i, j, 0);
        var newMax := if canMatch && currentLen > maxSoFar then currentLen else maxSoFar;
        MaxPreservableLength(s, t, i, j+1, newMax)
}

function MaxLongestSubsequence(s: string, t: string): int
    requires |s| == |t|
    requires |s| >= 0
    ensures MaxLongestSubsequence(s, t) >= 0
    ensures MaxLongestSubsequence(s, t) <= |s|
{
    if |s| == 0 then 0
    else MaxPreservableLength(s, t, 0, 0, 0)
}

lemma EmptyStringsHaveSameCharacterCounts()
    ensures HasSameCharacterCounts("", "")
{
    assert |""| == |""|;
    forall c ensures CountCharacter("", c) == CountCharacter("", c) {
        assert CountCharacter("", c) == 0;
    }
}

method solve(s: string, t: string) returns (result: int)
    requires |s| == |t|
    requires |s| >= 0
    ensures result == -1 <==> !HasSameCharacterCounts(s, t)
    ensures result >= -1
    ensures result != -1 ==> 0 <= result <= |s|
    ensures result != -1 ==> HasSameCharacterCounts(s, t)
    ensures result != -1 ==> result == |s| - MaxLongestSubsequence(s, t)
    ensures |s| == 0 ==> result == 0
{
    if |s| == 0 {
        EmptyStringsHaveSameCharacterCounts();
        assert HasSameCharacterCounts(s, t);
        result := 0;
        return;
    }

    if !HasSameCharacterCounts(s, t) {
        result := -1;
        return;
    }

    var maxSubseq := MaxLongestSubsequence(s, t);
    assert maxSubseq >= 0;
    assert maxSubseq <= |s|;
    result := |s| - maxSubseq;
    assert result >= 0;
    assert result <= |s|;
}
