// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix termination and proof issues */
function DecodeRleReal(lst: seq<(char, nat)>): seq<char>
    decreases |lst|
{
    if |lst| == 0 then []
    else RepeatChar(lst[0].0, lst[0].1) + DecodeRleReal(lst[1..])
}

function RepeatChar(c: char, n: nat): seq<char>
    decreases n
{
    if n == 0 then []
    else [c] + RepeatChar(c, n - 1)
}

lemma RepeatCharLength(c: char, n: nat)
    ensures |RepeatChar(c, n)| == n
    decreases n
{
    if n == 0 {
    } else {
        RepeatCharLength(c, n - 1);
    }
}

lemma DecodeRleEquivalence(result: seq<(char, nat)>)
    ensures DecodeRle(result) == DecodeRleReal(result)
    decreases |result|
{
    if |result| == 0 {
    } else {
        DecodeRleEquivalence(result[1..]);
    }
}

lemma SegmentEqualsRepeat(s: seq<char>, start: int, end: int, c: char)
    requires 0 <= start <= end <= |s|
    requires forall k :: start <= k < end ==> s[k] == c
    ensures s[start..end] == RepeatChar(c, end - start)
    decreases end - start
{
    if start == end {
    } else {
        SegmentEqualsRepeat(s, start + 1, end, c);
    }
}

lemma DecodeRleRealAppend(prefix: seq<(char, nat)>, suffix: seq<(char, nat)>)
    ensures DecodeRleReal(prefix + suffix) == DecodeRleReal(prefix) + DecodeRleReal(suffix)
    decreases |prefix|
{
    if |prefix| == 0 {
    } else {
        DecodeRleRealAppend(prefix[1..], suffix);
    }
}
// </vc-helpers>

// <vc-spec>
method RunLengthEncode(s: seq<char>) returns (result: seq<(char, nat)>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i].1 > 0
    ensures
        forall i :: 0 <= i < |result| ==> i + 1 < |result| ==> result[i].0 != result[i + 1].0
    ensures
        DecodeRle(result) == s
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix invariant and proof assertions */
    result := [];
    if |s| == 0 {
        DecodeRleEquivalence(result);
        return;
    }
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |result| ==> result[j].1 > 0
        invariant forall j :: 0 <= j <= |result| - 2 ==> result[j].0 != result[j + 1].0
        invariant DecodeRleReal(result) == s[..i]
    {
        var currentChar := s[i];
        var count := 1;
        var j := i + 1;
        
        while j < |s| && s[j] == currentChar
            invariant i < j <= |s|
            invariant count == j - i
            invariant count > 0
            invariant forall k :: i <= k < j ==> s[k] == currentChar
        {
            count := count + 1;
            j := j + 1;
        }
        
        assert count > 0;
        assert j > i;
        assert forall k :: i <= k < j ==> s[k] == currentChar;
        
        RepeatCharLength(currentChar, count);
        SegmentEqualsRepeat(s, i, j, currentChar);
        
        var oldResult := result;
        result := result + [(currentChar, count)];
        
        DecodeRleRealAppend(oldResult, [(currentChar, count)]);
        assert DecodeRleReal(result) == DecodeRleReal(oldResult) + DecodeRleReal([(currentChar, count)]);
        assert DecodeRleReal([(currentChar, count)]) == RepeatChar(currentChar, count);
        assert DecodeRleReal(oldResult) == s[..i];
        assert s[i..j] == RepeatChar(currentChar, count);
        assert s[..j] == s[..i] + s[i..j];
        assert DecodeRleReal(result) == s[..j];
        
        i := j;
    }
    
    DecodeRleEquivalence(result);
}
// </vc-code>
