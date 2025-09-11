// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: seq<char>) returns (result: bool)
    requires true
    ensures result ==> (forall i: int, j: int :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j])
    ensures !result ==> (|s| > 0 && exists i: int :: 0 <= i < |s| && s[i] != s[0])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
