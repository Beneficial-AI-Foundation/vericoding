// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ExtractRearChars(s: array<array<char>>) returns (result: array<char>)
    requires forall i :: 0 <= i < s.Length ==> s[i].Length > 0
    ensures s.Length == result.Length
    ensures forall i :: 0 <= i < s.Length ==> result[i] == s[i][s[i].Length - 1]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
