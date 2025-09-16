// <vc-preamble>
// ======= TASK =======
// Given a string, apply one of two transformations:
// 1. If the string contains at least one letter: swap the case of each letter (lowercase ↔ uppercase), keep non-letters unchanged
// 2. If the string contains no letters: reverse the entire string

// ======= SPEC REQUIREMENTS =======
function hasLetter(s: string): bool
{
    exists i :: 0 <= i < |s| && (('A' <= s[i] <= 'Z') || ('a' <= s[i] <= 'z'))
}

function reverseString(s: string): string
    ensures |reverseString(s)| == |s|
{
    if |s| == 0 then s else s[|s|-1..] + reverseString(s[..|s|-1])
}

function swapCase(c: char): char
{
    if 'A' <= c <= 'Z' then (c as int + 32) as char
    else if 'a' <= c <= 'z' then (c as int - 32) as char
    else c
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(s: string) returns (result: string)
    ensures if hasLetter(s) then
        |result| == |s| && 
        (forall i :: 0 <= i < |s| ==> result[i] == swapCase(s[i]))
    else
        result == reverseString(s)
    ensures |result| == |s|
// </vc-spec>
// <vc-code>
{
    if hasLetter(s) {
        var chars := [];
        var i := 0;

        while i < |s|
            invariant 0 <= i <= |s|
            invariant |chars| == i
            invariant forall j :: 0 <= j < i ==> chars[j] == swapCase(s[j])
        {
            if 'A' <= s[i] <= 'Z'
            {
                // Convert uppercase to lowercase
                var tmpCall1 := (s[i] as int + 32) as char;
                chars := chars + [tmpCall1];
            }
            else if 'a' <= s[i] <= 'z'
            {
                // Convert lowercase to uppercase  
                var tmpCall2 := (s[i] as int - 32) as char;
                chars := chars + [tmpCall2];
            }
            else
            {
                // Keep other characters unchanged
                chars := chars + [s[i]];
            }
            i := i + 1;
        }

        result := chars;
    } else {
        result := reverseString(s);
    }
}
// </vc-code>
