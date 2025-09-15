// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove faulty lemma and implement proper string reversal function */
function reverse_string(s: string): string
  ensures |reverse_string(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_string(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then
    ""
  else
    reverse_string(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use recursive helper function instead of iterative approach */
{
  rev := reverse_string(str);
}
// </vc-code>
