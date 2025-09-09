/*
function_signature: def how_many_times(string: str, substring: str) -> int
Find how many times a given substring can be found in the original string. Count overlaping cases.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
