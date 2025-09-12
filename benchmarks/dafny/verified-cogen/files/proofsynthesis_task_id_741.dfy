// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
