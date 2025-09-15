// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>
function reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else reverse(s[1..]) + [s[0]]
}

/* helper modified by LLM (iteration 2): added reverse function definition and lemma to prove reverse correctness */

lemma ReverseIsReverse(s: string)
  ensures |reverse(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse(s)[k] == s[|s| - 1 - k]
{
  if s != "" {
    var rec := reverse(s[1..]);
    ReverseIsReverse(s[1..]);
    // Dafny can complete the proof inductively
  }
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)

    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): append the reverse of s to s to create a palindrome, call lemma to assist verification */
  var rev := reverse(s);
  ReverseIsReverse(s);
  result := s + rev;
}
// </vc-code>
