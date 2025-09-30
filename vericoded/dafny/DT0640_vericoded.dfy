// <vc-preamble>
// Datatype to represent optional string
datatype OptionalString = None | Some(value: string)

// Predicate to check if a character is whitespace
predicate IsWhitespace(c: char)
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

// Predicate to check if a character is in a given character set
predicate CharInSet(c: char, chars: string)
{
    exists i :: 0 <= i < |chars| && chars[i] == c
}

// Predicate to check if a string consists only of characters from a given set
predicate AllCharsInSet(s: string, chars: string)
{
    forall i :: 0 <= i < |s| ==> CharInSet(s[i], chars)
}

// Predicate to check if a string consists only of whitespace characters
predicate AllWhitespace(s: string)
{
    forall i :: 0 <= i < |s| ==> IsWhitespace(s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, helper functions are correct */
function RStripSingle(s: string, chars: OptionalString): string
{
    if |s| == 0 then
        s
    else if chars.None? then
        if IsWhitespace(s[|s| - 1]) then
            RStripSingle(s[..|s| - 1], chars)
        else
            s
    else
        if CharInSet(s[|s| - 1], chars.value) then
            RStripSingle(s[..|s| - 1], chars)
        else
            s
}

lemma RStripSingleCorrect(s: string, chars: OptionalString)
    requires chars.Some? ==> |chars.value| >= 0
    ensures var r := RStripSingle(s, chars);
        chars.None? ==>
            (exists suffix :: s == r + suffix && AllWhitespace(suffix) &&
                (|r| == 0 || !IsWhitespace(r[|r| - 1])) && |r| <= |s|)
    ensures var r := RStripSingle(s, chars);
        chars.Some? ==>
            (exists suffix :: s == r + suffix && AllCharsInSet(suffix, chars.value) &&
                (|r| == 0 || !CharInSet(r[|r| - 1], chars.value)) && |r| <= |s|)
{
    var r := RStripSingle(s, chars);
    if |s| == 0 {
        assert r == s;
        assert s == r + "";
        assert AllWhitespace("");
        assert AllCharsInSet("", if chars.Some? then chars.value else "");
    } else if chars.None? {
        if IsWhitespace(s[|s| - 1]) {
            var r' := RStripSingle(s[..|s| - 1], chars);
            RStripSingleCorrect(s[..|s| - 1], chars);
            var suffix' :| s[..|s| - 1] == r' + suffix' && AllWhitespace(suffix') &&
                (|r'| == 0 || !IsWhitespace(r'[|r'| - 1])) && |r'| <= |s[..|s| - 1]|;
            assert r == r';
            var newSuffix := suffix' + [s[|s| - 1]];
            assert s == r + newSuffix;
            assert AllWhitespace(newSuffix);
        } else {
            assert r == s;
            assert s == r + "";
            assert AllWhitespace("");
            assert |r| > 0 && !IsWhitespace(r[|r| - 1]);
        }
    } else {
        if CharInSet(s[|s| - 1], chars.value) {
            var r' := RStripSingle(s[..|s| - 1], chars);
            RStripSingleCorrect(s[..|s| - 1], chars);
            var suffix' :| s[..|s| - 1] == r' + suffix' && AllCharsInSet(suffix', chars.value) &&
                (|r'| == 0 || !CharInSet(r'[|r'| - 1], chars.value)) && |r'| <= |s[..|s| - 1]|;
            assert r == r';
            var newSuffix := suffix' + [s[|s| - 1]];
            assert s == r + newSuffix;
            assert AllCharsInSet(newSuffix, chars.value);
        } else {
            assert r == s;
            assert s == r + "";
            assert AllCharsInSet("", chars.value);
            assert |r| > 0 && !CharInSet(r[|r| - 1], chars.value);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method RStrip(a: seq<string>, chars: OptionalString) returns (result: seq<string>)
    // Input sequence is well-formed
    requires |a| >= 0
    // Character set is well-formed when provided
    requires chars.Some? ==> |chars.value| >= 0
    
    // Output has same length as input
    ensures |result| == |a|
    
    // For each string in the sequence
    ensures forall i :: 0 <= i < |a| ==>
        // Case 1: When chars is None, whitespace is stripped
        (chars.None? ==> 
            (exists suffix :: 
                a[i] == result[i] + suffix &&
                AllWhitespace(suffix) &&
                (|result[i]| == 0 || !IsWhitespace(result[i][|result[i]| - 1])) &&
                |result[i]| <= |a[i]|)) &&
        
        // Case 2: When chars is provided, those characters are stripped  
        (chars.Some? ==>
            (exists suffix ::
                a[i] == result[i] + suffix &&
                AllCharsInSet(suffix, chars.value) &&
                (|result[i]| == 0 || !CharInSet(result[i][|result[i]| - 1], chars.value)) &&
                |result[i]| <= |a[i]|))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed postcondition verification by ensuring loop invariant holds for all indices */
{
    result := [];
    var idx := 0;
    while idx < |a|
        invariant 0 <= idx <= |a|
        invariant |result| == idx
        invariant forall i :: 0 <= i < idx ==>
            (chars.None? ==>
                (exists suffix :: a[i] == result[i] + suffix && AllWhitespace(suffix) &&
                    (|result[i]| == 0 || !IsWhitespace(result[i][|result[i]| - 1])) && |result[i]| <= |a[i]|))
        invariant forall i :: 0 <= i < idx ==>
            (chars.Some? ==>
                (exists suffix :: a[i] == result[i] + suffix && AllCharsInSet(suffix, chars.value) &&
                    (|result[i]| == 0 || !CharInSet(result[i][|result[i]| - 1], chars.value)) && |result[i]| <= |a[i]|))
    {
        var stripped := RStripSingle(a[idx], chars);
        RStripSingleCorrect(a[idx], chars);
        result := result + [stripped];
        idx := idx + 1;
    }
    assert forall i :: 0 <= i < |a| ==>
        (chars.None? ==>
            (exists suffix :: a[i] == result[i] + suffix && AllWhitespace(suffix) &&
                (|result[i]| == 0 || !IsWhitespace(result[i][|result[i]| - 1])) && |result[i]| <= |a[i]|));
    assert forall i :: 0 <= i < |a| ==>
        (chars.Some? ==>
            (exists suffix :: a[i] == result[i] + suffix && AllCharsInSet(suffix, chars.value) &&
                (|result[i]| == 0 || !CharInSet(result[i][|result[i]| - 1], chars.value)) && |result[i]| <= |a[i]|));
}
// </vc-code>
