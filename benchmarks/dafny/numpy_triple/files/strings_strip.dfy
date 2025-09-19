// <vc-preamble>
// Helper predicate to define whitespace characters
predicate IsWhitespace(c: char)
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\u000C' || c == '\u000B'
}

// Helper predicate to check if a character is in the removal set
predicate ShouldRemove(c: char, chars: string?)
{
    if chars == null then IsWhitespace(c)
    else c in chars
}

// Helper function to check if a string is a substring starting at given position
predicate IsSubstringAt(original: string, start: nat, len: nat, result: string)
{
    start + len <= |original| && 
    result == original[start..start + len]
}

// Helper predicate to check maximal leading removal
predicate MaximalLeadingRemoval(original: string, start: nat, chars: string?)
{
    (forall j :: 0 <= j < start ==> j < |original| && ShouldRemove(original[j], chars)) &&
    (start < |original| ==> !ShouldRemove(original[start], chars))
}

// Helper predicate to check maximal trailing removal  
predicate MaximalTrailingRemoval(original: string, start: nat, len: nat, chars: string?)
{
    (forall j :: start + len <= j < |original| ==> ShouldRemove(original[j], chars)) &&
    (len > 0 && start + len <= |original| ==> !ShouldRemove(original[start + len - 1], chars))
}

// Helper predicate for middle character preservation
predicate MiddlePreservation(original: string, result: string, start: nat)
{
    forall i, j :: 0 <= i < j < |result| ==> 
        start + i < |original| && start + j < |original| &&
        result[i] == original[start + i] && result[j] == original[start + j]
}
// Helper specification predicates for composition property
predicate IsLStripped(original: string, intermediate: string, chars: string?)
{
    exists k: nat :: k <= |original| &&
        intermediate == original[k..] &&
        (forall j :: 0 <= j < k && j < |original| ==> ShouldRemove(original[j], chars)) &&
        (k < |original| ==> !ShouldRemove(original[k], chars))
}

predicate IsRStripped(intermediate: string, result: string, chars: string?)
{
    exists suffix_len: nat :: suffix_len <= |intermediate| &&
        result == intermediate[..|intermediate| - suffix_len] &&
        (forall j :: |intermediate| - suffix_len <= j < |intermediate| ==> 
            ShouldRemove(intermediate[j], chars)) &&
        (suffix_len < |intermediate| ==> 
            !ShouldRemove(intermediate[|intermediate| - suffix_len - 1], chars))
}

// Reference function for whitespace stripping behavior
function StripWhitespace(s: string): string
{
    var start := FindFirstNonWhitespace(s, 0);
    if start >= |s| then ""
    else 
        var end := FindLastNonWhitespace(s, |s| - 1);
        s[start..end + 1]
}

function FindFirstNonWhitespace(s: string, pos: nat): nat
    decreases |s| - pos
{
    if pos >= |s| then pos
    else if !IsWhitespace(s[pos]) then pos
    else FindFirstNonWhitespace(s, pos + 1)
}

function FindLastNonWhitespace(s: string, pos: int): int
    decreases pos + 1
{
    if pos < 0 then -1
    else if !IsWhitespace(s[pos]) then pos
    else FindLastNonWhitespace(s, pos - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Strip(a: seq<string>, chars: string?) returns (result: seq<string>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==>
        var original := a[i];
        var stripped := result[i];
        // Length preservation or reduction
        |stripped| <= |original| &&
        // Empty string handling
        (|original| == 0 ==> stripped == "") &&
        // Substring property and character removal correctness
        (exists start: nat, len: nat ::
            IsSubstringAt(original, start, len, stripped) &&
            MaximalLeadingRemoval(original, start, chars) &&
            MaximalTrailingRemoval(original, start, len, chars) &&
            MiddlePreservation(original, stripped, start)) &&
        // Maximal stripping property
        (stripped == "" || 
         (!ShouldRemove(stripped[0], chars) && !ShouldRemove(stripped[|stripped| - 1], chars))) &&
        // Whitespace default behavior
        (chars == null ==> 
            stripped == StripWhitespace(original))
            
    ensures forall i :: 0 <= i < |a| ==>
        var original := a[i];
        var stripped := result[i];
        // Composition property: strip = rstrip(lstrip)
        exists intermediate: string ::
            IsLStripped(original, intermediate, chars) &&
            IsRStripped(intermediate, stripped, chars)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
