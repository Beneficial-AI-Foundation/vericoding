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
lemma CountCharacterSlice(s: string, c: char, i: int)
    requires 0 <= i < |s|
    ensures s[..i+1] == s[..i] + [s[i]]
    ensures s[i] == c ==> CountCharacter(s[..i+1], c) == CountCharacter(s[..i], c) + 1
    ensures s[i] != c ==> CountCharacter(s[..i+1], c) == CountCharacter(s[..i], c)
{
    assert s[..i+1] == s[..i] + [s[i]];
    var prefix := s[..i];
    var extended := s[..i+1];
    
    if s[i] == c {
        calc == {
            CountCharacter(extended, c);
            CountCharacter(prefix + [s[i]], c);
            { assert extended == prefix + [s[i]]; CountCharacterConcat(prefix, [s[i]], c); }
            CountCharacter(prefix, c) + CountCharacter([s[i]], c);
            { assert CountCharacter([c], c) == 1; }
            CountCharacter(prefix, c) + 1;
        }
    } else {
        calc == {
            CountCharacter(extended, c);
            CountCharacter(prefix + [s[i]], c);
            { assert extended == prefix + [s[i]]; CountCharacterConcat(prefix, [s[i]], c); }
            CountCharacter(prefix, c) + CountCharacter([s[i]], c);
            { assert s[i] != c; assert CountCharacter([s[i]], c) == 0; }
            CountCharacter(prefix, c) + 0;
            CountCharacter(prefix, c);
        }
    }
}

lemma CountCharacterConcat(s1: string, s2: string, c: char)
    ensures CountCharacter(s1 + s2, c) == CountCharacter(s1, c) + CountCharacter(s2, c)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc == {
            CountCharacter(s1 + s2, c);
            { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
            (if s1[0] == c then 1 else 0) + CountCharacter(s1[1..] + s2, c);
            { CountCharacterConcat(s1[1..], s2, c); }
            (if s1[0] == c then 1 else 0) + CountCharacter(s1[1..], c) + CountCharacter(s2, c);
            CountCharacter(s1, c) + CountCharacter(s2, c);
        }
    }
}

method HasSameCharacterCountsMethod(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures result == HasSameCharacterCounts(s, t)
{
    // Check if all characters in s appear with the same frequency in t
    var chars := CollectAllChars(s) + CollectAllChars(t);
    var i := 0;
    while i < |chars|
        invariant 0 <= i <= |chars|
        invariant forall j :: 0 <= j < i ==> CountCharacter(s, chars[j]) == CountCharacter(t, chars[j])
    {
        var c := chars[i];
        var countS := CountCharacterMethod(s, c);
        var countT := CountCharacterMethod(t, c);
        if countS != countT {
            return false;
        }
        i := i + 1;
    }
    
    // Prove that checking all chars in s and t is sufficient
    assert forall c :: c in chars ==> CountCharacter(s, c) == CountCharacter(t, c);
    CollectAllCharsContainsAll(s);
    CollectAllCharsContainsAll(t);
    assert forall c :: c in s ==> c in CollectAllChars(s);
    assert forall c :: c in t ==> c in CollectAllChars(t);
    assert forall c :: c in s ==> c in chars;
    assert forall c :: c in t ==> c in chars;
    CharCountsComplete(s, t, chars);
    return true;
}

function CollectAllChars(s: string): seq<char>
{
    if |s| == 0 then []
    else if s[0] in CollectAllChars(s[1..]) then CollectAllChars(s[1..])
    else [s[0]] + CollectAllChars(s[1..])
}

lemma CollectAllCharsContainsAll(s: string)
    ensures forall c :: c in s ==> c in CollectAllChars(s)
{
    if |s| == 0 {
        // trivially true
    } else {
        CollectAllCharsContainsAll(s[1..]);
        if s[0] in CollectAllChars(s[1..]) {
            assert CollectAllChars(s) == CollectAllChars(s[1..]);
        } else {
            assert CollectAllChars(s) == [s[0]] + CollectAllChars(s[1..]);
            assert s[0] in CollectAllChars(s);
        }
        forall c | c in s
        ensures c in CollectAllChars(s)
        {
            if c == s[0] {
                if s[0] in CollectAllChars(s[1..]) {
                    assert c in CollectAllChars(s);
                } else {
                    assert c in [s[0]] + CollectAllChars(s[1..]);
                }
            } else {
                assert c in s[1..];
                assert c in CollectAllChars(s[1..]);
                assert c in CollectAllChars(s);
            }
        }
    }
}

lemma CharCountsComplete(s: string, t: string, chars: seq<char>)
    requires |s| == |t|
    requires forall c :: c in s ==> c in chars
    requires forall c :: c in t ==> c in chars
    requires forall c :: c in chars ==> CountCharacter(s, c) == CountCharacter(t, c)
    ensures forall c :: CountCharacter(s, c) == CountCharacter(t, c)
{
    forall c
    ensures CountCharacter(s, c) == CountCharacter(t, c)
    {
        if CountCharacter(s, c) == 0 && CountCharacter(t, c) == 0 {
            // c doesn't appear in either string
        } else if CountCharacter(s, c) > 0 && CountCharacter(t, c) > 0 {
            // c appears in both strings
            CharInStringImpliesInChars(s, c);
            assert c in s;
            assert c in chars;
        } else if CountCharacter(s, c) > 0 {
            // c appears in s
            CharInStringImpliesInChars(s, c);
            assert c in s;
            assert c in chars;
        } else if CountCharacter(t, c) > 0 {
            // c appears in t
            CharInStringImpliesInChars(t, c);
            assert c in t;
            assert c in chars;
        }
    }
}

lemma CharInStringImpliesInChars(s: string, c: char)
    requires CountCharacter(s, c) > 0
    ensures c in s
{
    if |s| == 0 {
        assert CountCharacter(s, c) == 0;
        assert false;
    } else if s[0] == c {
        assert c in s;
    } else {
        assert CountCharacter(s[1..], c) > 0;
        CharInStringImpliesInChars(s[1..], c);
        assert c in s[1..];
        assert c in s;
    }
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
            CountCharacterSlice(s, c, i);
        } else {
            CountCharacterSlice(s, c, i);
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

