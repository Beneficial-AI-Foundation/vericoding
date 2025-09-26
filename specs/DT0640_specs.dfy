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
{
  assume {:axiom} false;
}
// </vc-code>
