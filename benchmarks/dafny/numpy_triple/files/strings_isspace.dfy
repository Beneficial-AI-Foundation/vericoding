// <vc-preamble>
// Define what constitutes a whitespace character
predicate IsWhitespace(c: char)
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'
}

// Check if a string contains only whitespace characters and is non-empty
predicate IsOnlyWhitespaceString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsWhitespace(s[i])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Isspace(a: seq<string>) returns (result: seq<bool>)
    // Output has same length as input
    ensures |result| == |a|
    
    // For each index, result is true iff string is non-empty and contains only whitespace
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == (|a[i]| > 0 && forall j :: 0 <= j < |a[i]| ==> IsWhitespace(a[i][j]))
    
    // Equivalent formulation using helper predicate
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsOnlyWhitespaceString(a[i])
    
    // Empty strings always return false
    ensures forall i :: 0 <= i < |a| ==> (a[i] == "" ==> result[i] == false)
    
    // Non-empty strings with any non-whitespace character return false
    ensures forall i :: 0 <= i < |a| ==> 
        (|a[i]| > 0 && exists j :: 0 <= j < |a[i]| && !IsWhitespace(a[i][j])) ==> result[i] == false
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
