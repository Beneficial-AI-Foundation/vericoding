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

// <vc-helpers>
lemma FindNextMatchInRange(s: string, c: char, start: int, endIndex: int)
    requires 0 <= start <= endIndex <= |s|
    ensures exists k :: start <= k <= endIndex && ((k < |s| ==> s[k] == c) || (k == |s| && c !in s[start..endIndex]))
    decreases endIndex - start
{
    if start == endIndex {
        // k = endIndex, which is |s| if endIndex = |s|, or within range otherwise
    } else {
        if s[start] == c {
            // Found at start
        } else {
            FindNextMatchInRange(s, c, start+1, endIndex);
        }
    }
}

lemma CanMatchSubstringPreservesCounts(s: string, t: string, i: int, j: int, k: int)
    requires 0 <= i <= j < |t|
    requires 0 <= k <= |s|
    requires |s| == |t|
    requires CanMatchSubstring(s, t, i, j, k)
    ensures CountCharacter(s[k..], t[j]) >= 1
    decreases j - i + 1, |s| - k
{
    var nextK := FindNextMatch(s, t[j], k);
    if i == j {
        assert nextK < |s|; // Since CanMatchSubstring returned true
        assert s[nextK] == t[j];
        // Explicitly show count >= 1
        var substr := s[k..];
        assert |substr| > nextK - k;
        assert substr[nextK - k] == t[j];
    } else {
        CanMatchSubstringPreservesCounts(s, t, i, j-1, nextK+1);
    }
}

lemma MaxPreservableLengthCorrect(s: string, t: string, i: int, j: int, maxSoFar: int)
    requires 0 <= i <= |t|
    requires i <= j <= |t|
    requires |s| == |t|
    requires maxSoFar >= 0
    requires maxSoFar <= |s|
    decreases |t| - i, |t| - j
    ensures MaxPreservableLength(s, t, i, j, maxSoFar) == maxSoFar || 
            (exists k :: 0 <= k <= |s| && CanMatchSubstring(s, t, i, j, k))
{
    if i >= |t| {
    } else if j >= |t| {
        MaxPreservableLengthCorrect(s, t, i+1, i+1, maxSoFar);
    } else {
        var currentLen := j - i + 1;
        var canMatch := CanMatchSubstring(s, t, i, j, 0);
        var newMax := if canMatch && currentLen > maxSoFar then currentLen else maxSoFar;
        if canMatch {
            // Witness exists: k = 0 works
        }
        MaxPreservableLengthCorrect(s, t, i, j+1, newMax);
    }
}

lemma MaxPreservableLengthMatchesMaxLongestSubsequence(s: string, t: string)
    requires |s| == |t|
    ensures MaxPreservableLength(s, t, 0, 0, 0) == MaxLongestSubsequence(s, t)
{
    // Helper lemma to connect the two functions
    if |s| == 0 {
    } else {
        // The recursive structure matches, so the results should be equal
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, t: string) returns (result: int)
    requires |s| == |t|
    requires |s| >= 0
    ensures result == -1 <==> !HasSameCharacterCounts(s, t)
    ensures result >= -1
    ensures result != -1 ==> 0 <= result <= |s|
    ensures result != -1 ==> HasSameCharacterCounts(s, t)
    ensures result != -1 ==> result == |s| - MaxLongestSubsequence(s, t)
    ensures |s| == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        result := 0;
    } else {
        if !HasSameCharacterCounts(s, t) {
            result := -1;
        } else {
            var maxLen := MaxPreservableLength(s, t, 0, 0, 0);
            result := |s| - maxLen;
            MaxPreservableLengthMatchesMaxLongestSubsequence(s, t);
            assert maxLen == MaxLongestSubsequence(s, t);
        }
    }
}
// </vc-code>

