// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountChar(chars: seq<char>, c: char): nat
    decreases |chars|
{
    if |chars| == 0 then
        0
    else if chars[0] == c then
        1 + CountChar(chars[1..], c)
    else
        CountChar(chars[1..], c)
}

predicate HasNoDuplicatesUpTo(chars: seq<char>, endIdx: int)
    requires 0 <= endIdx <= |chars|
{
    forall i, j :: 0 <= i < j < endIdx ==> chars[i] != chars[j]
}

predicate HasNoDuplicates(chars: seq<char>)
{
    forall i, j :: 0 <= i < j < |chars| ==> chars[i] != chars[j]
}

function FirstOccurrenceIndex(chars: seq<char>, c: char): int
    requires exists i :: 0 <= i < |chars| && chars[i] == c
    ensures 0 <= FirstOccurrenceIndex(chars, c) < |chars|
    ensures chars[FirstOccurrenceIndex(chars, c)] == c
{
    if chars[0] == c then 0
    else 1 + FirstOccurrenceIndex(chars[1..], c)
}

predicate SecondOccurrenceExists(chars: seq<char>, c: char)
{
    exists i, j :: 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed CountCharPrefix lemma to properly handle all cases */
lemma CountCharIncrease(chars: seq<char>, c: char, newChar: char)
    ensures CountChar(chars + [newChar], c) == CountChar(chars, c) + (if newChar == c then 1 else 0)
{
    if |chars| == 0 {
        assert chars + [newChar] == [newChar];
    } else {
        assert (chars + [newChar])[0] == chars[0];
        assert (chars + [newChar])[1..] == chars[1..] + [newChar];
        CountCharIncrease(chars[1..], c, newChar);
    }
}

lemma CountCharPrefix(s: seq<char>, i: int, c: char)
    requires 0 <= i <= |s|
    ensures CountChar(s[..i], c) <= CountChar(s, c)
{
    if i == |s| {
        assert s[..i] == s;
    } else if i == 0 {
        assert s[..i] == [];
        assert CountChar(s[..i], c) == 0;
    } else {
        // Handle the recursive case properly
        var prefix := s[..i];
        var tail := s[i..];
        assert s == prefix + tail;
        CountCharConcat(prefix, tail, c);
    }
}

lemma CountCharConcat(s1: seq<char>, s2: seq<char>, c: char)
    ensures CountChar(s1 + s2, c) == CountChar(s1, c) + CountChar(s2, c)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        CountCharConcat(s1[1..], s2, c);
    }
}

lemma FindFirstOccurrence(s: seq<char>, c: char, i: int) returns (idx: int)
    requires 0 <= i <= |s|
    requires c in s[..i]
    ensures 0 <= idx < i
    ensures s[idx] == c
    ensures forall j :: 0 <= j < idx ==> s[j] != c
{
    var k := 0;
    while k < i
        invariant 0 <= k <= i
        invariant forall j :: 0 <= j < k ==> s[j] != c
        invariant c in s[k..i]
    {
        if s[k] == c {
            idx := k;
            return;
        }
        k := k + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: array<char>) returns (result: Option<char>)
    ensures match result {
        case Some(c) => 
            var chars := s[..];
            CountChar(chars, c) >= 2 &&
            SecondOccurrenceExists(chars, c) &&
            (exists firstIdx :: 0 <= firstIdx < |chars| && chars[firstIdx] == c &&
             exists secondIdx :: firstIdx < secondIdx < |chars| && chars[secondIdx] == c &&
             HasNoDuplicatesUpTo(chars, secondIdx))
        case None => 
            HasNoDuplicates(s[..])
    }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant and postcondition verification */
{
    var seen := {};
    var i := 0;
    
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall c :: c in seen ==> exists j :: 0 <= j < i && s[j] == c
        invariant forall j :: 0 <= j < i ==> s[j] in seen
        invariant forall c :: c in seen ==> CountChar(s[..i], c) >= 1
        invariant forall j, k :: 0 <= j < k < i ==> s[j] != s[k]
    {
        if s[i] in seen {
            // Found the first repeated character
            var firstIdx := FindFirstOccurrence(s[..], s[i], i);
            
            assert 0 <= firstIdx < i;
            assert s[firstIdx] == s[i];
            assert forall j :: 0 <= j < firstIdx ==> s[j] != s[i];
            assert firstIdx < i < s.Length;
            assert s[i] == s[firstIdx];
            
            // The character appears at least twice
            assert s[..i+1][firstIdx] == s[i];
            assert s[..i+1][i] == s[i];
            assert firstIdx < i < i+1;
            
            // Use lemma to show CountChar increases properly
            var prefix := s[..i];
            assert s[..i+1] == prefix + [s[i]];
            CountCharIncrease(prefix, s[i], s[i]);
            assert CountChar(s[..i+1], s[i]) == CountChar(prefix, s[i]) + 1;
            assert CountChar(prefix, s[i]) >= 1;
            assert CountChar(s[..i+1], s[i]) >= 2;
            
            CountCharPrefix(s[..], i+1, s[i]);
            assert CountChar(s[..], s[i]) >= CountChar(s[..i+1], s[i]);
            assert CountChar(s[..], s[i]) >= 2;
            
            // Second occurrence exists
            assert SecondOccurrenceExists(s[..], s[i]);
            
            // Has no duplicates up to the second occurrence
            assert forall j, k :: 0 <= j < k < i ==> s[j] != s[k];
            assert HasNoDuplicatesUpTo(s[..], i);
            
            // Verify postcondition format with proper parentheses
            assert exists fIdx :: 0 <= fIdx < |s[..]| && s[..][fIdx] == s[i] &&
                   (exists sIdx :: fIdx < sIdx < |s[..]| && s[..][sIdx] == s[i] &&
                    HasNoDuplicatesUpTo(s[..], sIdx));
            
            result := Some(s[i]);
            return;
        }
        
        // Maintain invariants when adding new character
        assert s[i] !in seen;
        assert forall j :: 0 <= j < i ==> s[j] != s[i];
        
        seen := seen + {s[i]};
        i := i + 1;
    }
    
    assert i == s.Length;
    assert forall j, k :: 0 <= j < k < s.Length ==> s[j] != s[k];
    assert HasNoDuplicates(s[..]);
    result := None;
}
// </vc-code>
