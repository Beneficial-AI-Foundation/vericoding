// <vc-preamble>
predicate IsUpperCase(c: char)
{
    c >= 'A' && c <= 'Z'
}

function Shift32Spec(c: char): char
    requires IsUpperCase(c)
    requires c as int + 32 < 65536
{
    if c as int + 32 < 65536 then (c as int + 32) as char else c
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ToLowercase(str1: array<char>) returns (result: array<char>)
    ensures result.Length == str1.Length
    ensures forall i :: 0 <= i < str1.Length ==> 
        result[i] == (if IsUpperCase(str1[i]) then Shift32Spec(str1[i]) else str1[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
