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
/* helper modified by LLM (iteration 5): fixed suffix existence validation and precondition propagation */
function SecondOccurrenceIndex(chars: seq<char>, c: char): int
    requires SecondOccurrenceExists(chars, c)
    ensures 0 <= SecondOccurrenceIndex(chars, c) < |chars|
    ensures chars[SecondOccurrenceIndex(chars, c)] == c
    ensures exists firstIdx :: 0 <= firstIdx < SecondOccurrenceIndex(chars, c) && chars[firstIdx] == c
{
    var firstIdx := FirstOccurrenceIndex(chars, c);
    if firstIdx + 1 < |chars| && chars[firstIdx + 1] == c then
        firstIdx + 1
    else
        var suffix := chars[firstIdx + 1..];
        assert exists i, j :: 0 <= i < j < |chars| && chars[i] == c && chars[j] == c;
        var witness_i, witness_j :| 0 <= witness_i < witness_j < |chars| && chars[witness_i] == c && chars[witness_j] == c;
        assert witness_j > firstIdx;
        assert witness_j >= firstIdx + 1;
        assert witness_j - (firstIdx + 1) < |suffix|;
        assert chars[witness_j] == c;
        assert suffix[witness_j - (firstIdx + 1)] == c;
        assert exists k :: 0 <= k < |suffix| && suffix[k] == c;
        firstIdx + 1 + FirstOccurrenceIndex(suffix, c)
}

lemma SecondOccurrenceExistenceHelper(chars: seq<char>, c: char)
    requires exists i, j :: 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
    ensures SecondOccurrenceExists(chars, c)
{
}

lemma CountCharProperty(chars: seq<char>, c: char, firstIdx: int, secondIdx: int)
    requires 0 <= firstIdx < secondIdx < |chars|
    requires chars[firstIdx] == c && chars[secondIdx] == c
    ensures CountChar(chars, c) >= 2
{
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
    /* code modified by LLM (iteration 5): simplified approach with direct duplicate detection */
    var chars := s[..];
    var i := 0;
    
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant HasNoDuplicatesUpTo(chars, i)
    {
        var c := s[i];
        var j := 0;
        var found := false;
        
        while j < i && !found
            invariant 0 <= j <= i
            invariant !found ==> forall k :: 0 <= k < j ==> chars[k] != c
            invariant found ==> exists k :: 0 <= k < j && chars[k] == c
        {
            if s[j] == c {
                found := true;
                assert chars[j] == c && chars[i] == c && j < i;
                assert SecondOccurrenceExists(chars, c);
                CountCharProperty(chars, c, j, i);
                result := Some(c);
                return;
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    result := None;
}
// </vc-code>
