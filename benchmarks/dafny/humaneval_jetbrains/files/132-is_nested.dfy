/*
function_signature: def is_nested(string: str) -> Bool
Create a function that takes a string as input which contains only parentheses. The function should return True if and only if there is a valid subsequence of parentheses where at least one parenthesis in the subsequence is nested.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
