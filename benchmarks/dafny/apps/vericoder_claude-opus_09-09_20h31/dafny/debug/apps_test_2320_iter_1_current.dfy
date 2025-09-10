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
method HasSameCharacterCountsMethod(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures result == HasSameCharacterCounts(s, t)
{
    // For simplicity, we'll check all ASCII characters
    var i := 0;
    while i < 256
        invariant 0 <= i <= 256
        invariant forall c :: 0 <= c as int < i ==> CountCharacter(s, c as char) == CountCharacter(t, c as char)
    {
        var c := i as char;
        var countS := CountCharacterMethod(s, c);
        var countT := CountCharacterMethod(t, c);
        if countS != countT {
            return false;
        }
        i := i + 1;
    }
    return true;
}

method CountCharacterMethod(s: string, c: char) returns (count: int)
    ensures count == CountCharacter(s, c)
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == CountCharacter(s[..i], c)
    {
        if s[i] == c {
            count := count + 1;
        }
        i := i + 1;
    }
    assert s[..|s|] == s;
}

method ComputeMaxLongestSubsequence(s: string, t: string) returns (maxLen: int)
    requires |s| == |t|
    requires |s| >= 0
    ensures maxLen == MaxLongestSubsequence(s, t)
{
    if |s| == 0 {
        return 0;
    }
    maxLen := ComputeMaxPreservableLength(s, t, 0, 0, 0);
}

method ComputeMaxPreservableLength(s: string, t: string, i: int, j: int, maxSoFar: int) returns (maxLen: int)
    requires 0 <= i <= |t|
    requires i <= j <= |t|
    requires |s| == |t|
    requires maxSoFar >= 0
    requires maxSoFar <= |s|
    ensures maxLen == MaxPreservableLength(s, t, i, j, maxSoFar)
    decreases |t| - i, |t| - j
{
    if i >= |t| {
        return maxSoFar;
    } else if j >= |t| {
        maxLen := ComputeMaxPreservableLength(s, t, i+1, i+1, maxSoFar);
        return;
    } else {
        var currentLen := j - i + 1;
        var canMatch := ComputeCanMatchSubstring(s, t, i, j, 0);
        var newMax := if canMatch && currentLen > maxSoFar then currentLen else maxSoFar;
        maxLen := ComputeMaxPreservableLength(s, t, i, j+1, newMax);
    }
}

method ComputeCanMatchSubstring(s: string, t: string, i: int, j: int, k: int) returns (canMatch: bool)
    requires 0 <= i <= j < |t|
    requires 0 <= k <= |s|
    requires |s| == |t|
    ensures canMatch == CanMatchSubstring(s, t, i, j, k)
    decreases j - i + 1, |s| - k
{
    if i > j {
        return true;
    } else if k >= |s| {
        return false;
    } else {
        var nextK := ComputeFindNextMatch(s, t[j], k);
        if nextK >= |s| {
            return false;
        } else if i == j {
            return true;
        } else {
            assert nextK < |s|;
            canMatch := ComputeCanMatchSubstring(s, t, i, j-1, nextK+1);
        }
    }
}

method ComputeFindNextMatch(s: string, c: char, start: int) returns (pos: int)
    requires 0 <= start <= |s|
    ensures pos == FindNextMatch(s, c, start)
    ensures start <= pos <= |s|
    decreases |s| - start
{
    if start >= |s| {
        return |s|;
    } else if s[start] == c {
        return start;
    } else {
        pos := ComputeFindNextMatch(s, c, start + 1);
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
        return 0;
    }
    
    var hasSameCounts := HasSameCharacterCountsMethod(s, t);
    
    if !hasSameCounts {
        return -1;
    }
    
    var maxSubseq := ComputeMaxLongestSubsequence(s, t);
    result := |s| - maxSubseq;
}
// </vc-code>

