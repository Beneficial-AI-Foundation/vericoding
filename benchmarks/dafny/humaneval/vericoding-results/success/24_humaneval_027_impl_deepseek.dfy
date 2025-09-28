// <vc-preamble>

predicate IsLowercase(c: char) {
    'a' <= c <= 'z'
}

predicate IsUppercase(c: char) {
    'A' <= c <= 'Z'
}

function FlipChar(c: char): char {
    if IsLowercase(c) then c - 'a' + 'A'
    else if IsUppercase(c) then c - 'A' + 'a'
    else c
}

predicate ValidFlipCase(s: string, result: string) {
    |result| == |s| &&
    forall i :: 0 <= i < |s| ==> result[i] == FlipChar(s[i])
}
// </vc-preamble>

// <vc-helpers>

predicate ValidResultString(s: string, result: string)
{
    |result| == |s| &&
    forall i | 0 <= i < |s| :: result[i] == FlipChar(s[i])
}

lemma FlipCharLemma(c: char)
    ensures FlipChar(FlipChar(c)) == c
{
    // No body needed for lemma, Dafny can prove this automatically
}

lemma StringIndexInvariant(s: string, result: string, i: int)
    requires 0 <= i <= |s|
    requires |result| == i
    requires forall j | 0 <= j < i :: result[j] == FlipChar(s[j])
{
}

// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (result: string)
    ensures ValidFlipCase(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed string building with array approach */
    var chars := new char[|s|];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j | 0 <= j < i :: chars[j] == FlipChar(s[j])
    {
        chars[i] := FlipChar(s[i]);
        i := i + 1;
    }
    
    result := chars[..];
}
// </vc-code>
