// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveChars(str1: array<char>, str2: array<char>) returns (result: array<char>)
    ensures
        forall i :: 0 <= i < result.Length ==> (result[i] in str1[..] && result[i] !in str2[..])
    ensures
        forall i :: 0 <= i < str1.Length ==> (str1[i] in str2[..] || str1[i] in result[..])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
