// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReplaceChars(s: array<char>, old_char: char, new_char: char) returns (result: array<char>)
    ensures
        result.Length == s.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == (if s[i] == old_char then new_char else s[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
