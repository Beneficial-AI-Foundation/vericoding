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
function CountCharacterMethod(s: string, c: char): int
{
    CountCharacter(s, c)
}

function HasSameCharacterCountsMethod(s: string, t: string): bool
{
    HasSameCharacterCounts(s, t)
}

function MaxLongestSubsequenceMethod(s: string, t: string): int
    requires |s| == |t|
    requires |s| >= 0
{
    MaxLongestSubsequence(s, t)
}

lemma CharacterCountsDecidable(s: string, t: string)
    requires |s| == |t|
    ensures HasSameCharacterCounts(s, t) <==> 
        (forall c :: CountCharacter(s, c) == CountCharacter(t, c))
{
}

function GetAllCharsInStrings(s: string, t: string): set<char>
{
    (set i | 0 <= i < |s| :: s[i]) + (set i | 0 <= i < |t| :: t[i])
}

function CheckCharacterCountsFinite(s: string, t: string, chars: seq<char>, index: int): bool
    requires |s| == |t|
    requires 0 <= index <= |chars|
    decreases |chars| - index
{
    if index >= |chars| then true
    else if CountCharacter(s, chars[index]) != CountCharacter(t, chars[index]) then false
    else CheckCharacterCountsFinite(s, t, chars, index + 1)
}

lemma FiniteCharacterCheck(s: string, t: string, chars: seq<char>)
    requires |s| == |t|
    requires forall c :: c in GetAllCharsInStrings(s, t) ==> c in chars
    ensures CheckCharacterCountsFinite(s, t, chars, 0) <==> HasSameCharacterCounts(s, t)
{
    if CheckCharacterCountsFinite(s, t, chars, 0) {
        assert forall c :: CountCharacter(s, c) == CountCharacter(t, c);
    } else {
        var index := FindMismatchIndex(s, t, chars, 0);
        assert index < |chars|;
        assert CountCharacter(s, chars[index]) != CountCharacter(t, chars[index]);
        assert !HasSameCharacterCounts(s, t);
    }
}

function FindMismatchIndex(s: string, t: string, chars: seq<char>, index: int): int
    requires |s| == |t|
    requires 0 <= index <= |chars|
    requires !CheckCharacterCountsFinite(s, t, chars, index)
    ensures index <= FindMismatchIndex(s, t, chars, index) < |chars|
    decreases |chars| - index
{
    if CountCharacter(s, chars[index]) != CountCharacter(t, chars[index]) then index
    else FindMismatchIndex(s, t, chars, index + 1)
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
        return 0;
    }
    
    // Get all unique characters from both strings
    var allChars: seq<char> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] in allChars
    {
        if s[i] !in allChars {
            allChars := allChars + [s[i]];
        }
        i := i + 1;
    }
    
    i := 0;
    while i < |t|
        invariant 0 <= i <= |t|
        invariant forall j :: 0 <= j < |s| ==> s[j] in allChars
        invariant forall j :: 0 <= j < i ==> t[j] in allChars
    {
        if t[i] !in allChars {
            allChars := allChars + [t[i]];
        }
        i := i + 1;
    }
    
    // Check if character counts match
    var charIndex := 0;
    while charIndex < |allChars|
        invariant 0 <= charIndex <= |allChars|
        invariant forall k :: 0 <= k < charIndex ==> CountCharacter(s, allChars[k]) == CountCharacter(t, allChars[k])
    {
        var countS := CountCharacterMethod(s, allChars[charIndex]);
        var countT := CountCharacterMethod(t, allChars[charIndex]);
        if countS != countT {
            return -1;
        }
        charIndex := charIndex + 1;
    }
    
    // If we reach here, character counts match
    var maxSubseq := MaxLongestSubsequenceMethod(s, t);
    result := |s| - maxSubseq;
}
// </vc-code>

