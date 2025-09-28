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
/* helper modified by LLM (iteration 5): Fixed recursive call indices in CountCharAtLeastTwo */
lemma CountCharZero(chars: seq<char>, c: char)
    ensures c !in chars ==> CountChar(chars, c) == 0
{
    if |chars| == 0 {
    } else if chars[0] == c {
    } else {
        CountCharZero(chars[1..], c);
    }
}

lemma CountCharAtLeastTwo(chars: seq<char>, c: char, i: int, j: int)
    requires 0 <= i < j < |chars|
    requires chars[i] == c && chars[j] == c
    ensures CountChar(chars, c) >= 2
{
    if i == 0 {
        assert chars[0] == c;
        if j == 1 {
            assert chars[1] == c;
            assert CountChar(chars, c) >= 1 + CountChar(chars[1..], c);
            assert CountChar(chars[1..], c) >= 1;
        } else {
            assert j - 1 >= 0;
            assert j - 1 < |chars[1..]|;
            assert chars[1..][j-1] == chars[j];
            var k := 0;
            while k < j - 1
                invariant 0 <= k <= j - 1
            {
                if chars[1..][k] == c {
                    CountCharAtLeastTwo(chars[1..], c, k, j-1);
                    return;
                }
                k := k + 1;
            }
            assert chars[1..][j-1] == c;
            CountCharAtLeastTwo(chars[1..], c, j-1, j-1);
        }
    } else {
        CountCharAtLeastTwo(chars[1..], c, i-1, j-1);
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
/* code modified by LLM (iteration 5): Fixed loop invariant and simplified logic */
{
    var seen := {};
    var i := 0;
    
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall c :: c in seen ==> exists k :: 0 <= k < i && s[k] == c
        invariant forall k :: 0 <= k < i ==> s[k] in seen || (exists j :: 0 <= j < k && s[j] == s[k])
        invariant forall j, k :: 0 <= j < k < i && s[k] !in seen[..j] ==> s[j] != s[k]
        invariant HasNoDuplicatesUpTo(s[..], i) || (exists j, k :: 0 <= j < k < i && s[j] == s[k])
    {
        if s[i] in seen {
            var firstIdx := 0;
            while firstIdx < i
                invariant 0 <= firstIdx <= i
                decreases i - firstIdx
            {
                if s[firstIdx] == s[i] {
                    assert 0 <= firstIdx < i < s.Length;
                    assert s[firstIdx] == s[i] && s[i] == s[i];
                    CountCharAtLeastTwo(s[..], s[i], firstIdx, i);
                    result := Some(s[i]);
                    return;
                }
                firstIdx := firstIdx + 1;
            }
        }
        seen := seen + {s[i]};
        i := i + 1;
    }
    
    result := None;
}
// </vc-code>
