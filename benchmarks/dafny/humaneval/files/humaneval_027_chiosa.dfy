// <vc-preamble>
// ======= TASK =======
// Given a string, convert all lowercase letters to uppercase and all uppercase letters to lowercase. 
// Non-alphabetic characters remain unchanged.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method flip_case(s: string) returns (result: string)
    ensures ValidFlipCase(s, result)
// </vc-spec>
// <vc-code>
{
    result := "";
    for i := 0 to |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == FlipChar(s[j])
    {
        var c := s[i];
        if 'a' <= c && c <= 'z' {
            result := result + [c - 'a' + 'A'];
        } else if 'A' <= c && c <= 'Z' {
            result := result + [c - 'A' + 'a'];
        } else {
            result := result + [c];
        }
    }
}
// </vc-code>
