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
/* helper modified by LLM (iteration 5): Fixed postcondition conditions and termination */
lemma CountCharProperty(chars: seq<char>, c: char, i: int)
    requires 0 <= i < |chars|
    requires chars[i] == c
    ensures CountChar(chars[..i+1], c) == CountChar(chars[..i], c) + 1
{
    if i == 0 {
        assert chars[..1] == [chars[0]];
        assert chars[0] == c;
        assert CountChar(chars[..1], c) == 1;
        assert CountChar(chars[..0], c) == 0;
    } else {
        assert chars[..i+1] == chars[..i] + [chars[i]];
        assert chars[i] == c;
        assert CountChar(chars[..i+1], c) == CountChar(chars[..i], c) + CountChar([chars[i]], c);
        assert CountChar([chars[i]], c) == 1;
    }
}

lemma CountCharSequential(chars: seq<char>, c: char, i: int)
    requires 0 <= i < |chars|
    requires chars[i] != c
    ensures CountChar(chars[..i+1], c) == CountChar(chars[..i], c)
{
    if i == 0 {
        assert chars[..1] == [chars[0]];
        assert chars[0] != c;
        assert CountChar(chars[..1], c) == 0;
        assert CountChar(chars[..0], c) == 0;
    } else {
        assert chars[..i+1] == chars[..i] + [chars[i]];
        assert chars[i] != c;
        assert CountChar(chars[..i+1], c) == CountChar(chars[..i], c) + CountChar([chars[i]], c);
        assert CountChar([chars[i]], c) == 0;
    }
}

lemma CountCharMonotonic(chars: seq<char>, c: char, i: int)
    requires 0 <= i < |chars|
    ensures CountChar(chars[..i+1], c) <= CountChar(chars, c)
    decreases |chars| - i
{
    if i == |chars| - 1 {
        assert chars[..i+1] == chars;
    } else {
        CountCharMonotonic(chars, c, i + 1);
        assert CountChar(chars[..i+2], c) <= CountChar(chars, c);
        if chars[i+1] == c {
            assert CountChar(chars[..i+2], c) == CountChar(chars[..i+1], c) + 1;
        } else {
            assert CountChar(chars[..i+2], c) == CountChar(chars[..i+1], c);
        }
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
{
    /* code modified by LLM (iteration 5): Fixed invariant and count tracking */
    var chars := s[..];
    var seen: set<char> := {};
    
    for i := 0 to s.Length
        invariant 0 <= i <= s.Length
        invariant seen == set j | 0 <= j < i :: chars[j]
        invariant HasNoDuplicatesUpTo(chars, i)
        invariant forall c :: c in seen ==> (exists! j :: 0 <= j < i && chars[j] == c)
    {
        if s[i] in seen {
            result := Some(s[i]);
            assert s[i] in seen;
            assert exists j :: 0 <= j < i && chars[j] == s[i];
            assert chars[i] == s[i];
            assert exists j :: 0 <= j < i && j != i && chars[j] == chars[i];
            CountCharProperty(chars, s[i], i);
            assert CountChar(chars[..i+1], s[i]) >= 2;
            return;
        }
        seen := seen + {s[i]};
    }
    
    result := None;
}
// </vc-code>
