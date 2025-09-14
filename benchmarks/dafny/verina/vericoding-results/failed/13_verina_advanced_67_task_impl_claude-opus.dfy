// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed duplicate DecodeRle definition */
lemma DecodeRleAppend(lst1: seq<(char, nat)>, lst2: seq<(char, nat)>)
    ensures DecodeRle(lst1 + lst2) == DecodeRle(lst1) + DecodeRle(lst2)
    decreases lst1
{
    if |lst1| == 0 {
        assert lst1 + lst2 == lst2;
    } else if lst1[0].1 == 0 {
        DecodeRleAppend(lst1[1..], lst2);
    } else {
        var rest := [(lst1[0].0, lst1[0].1 - 1)] + lst1[1..];
        DecodeRleAppend(rest, lst2);
    }
}

lemma DecodeRleSingle(c: char, n: nat)
    requires n > 0
    ensures DecodeRle([(c, n)]) == seq(n, i => c)
    decreases n
{
    if n == 1 {
        assert DecodeRle([(c, 1)]) == [c] + DecodeRle([(c, 0)] + []);
        assert DecodeRle([(c, 0)]) == DecodeRle([]);
        assert DecodeRle([]) == [];
        assert [c] == seq(1, i => c);
    } else {
        DecodeRleSingle(c, n - 1);
        assert DecodeRle([(c, n)]) == [c] + DecodeRle([(c, n - 1)]);
        assert DecodeRle([(c, n - 1)]) == seq(n - 1, i => c);
        assert [c] + seq(n - 1, i => c) == seq(n, i => c);
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
    /* code modified by LLM (iteration 4): Implementation of run-length encoding */
    result := [];
    if |s| == 0 {
        return;
    }
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |result| ==> result[j].1 > 0
        invariant forall j :: 0 <= j < |result| ==> j + 1 < |result| ==> result[j].0 != result[j + 1].0
        invariant DecodeRle(result) == s[..i]
    {
        var currentChar := s[i];
        var count := 1;
        var j := i + 1;
        
        while j < |s| && s[j] == currentChar
            invariant i < j <= |s|
            invariant count == j - i
            invariant forall k :: i <= k < j ==> s[k] == currentChar
        {
            count := count + 1;
            j := j + 1;
        }
        
        var old_result := result;
        result := result + [(currentChar, count)];
        
        DecodeRleSingle(currentChar, count);
        DecodeRleAppend(old_result, [(currentChar, count)]);
        assert DecodeRle(result) == DecodeRle(old_result) + DecodeRle([(currentChar, count)]);
        assert DecodeRle([(currentChar, count)]) == seq(count, k => currentChar);
        assert s[i..j] == seq(count, k => currentChar);
        assert DecodeRle(result) == s[..i] + s[i..j];
        assert s[..i] + s[i..j] == s[..j];
        
        i := j;
    }
    
    assert i == |s|;
    assert s[..i] == s;
}
// </vc-code>
