// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removing duplicate function definition and keeping only helper lemma */
lemma palindrome_helper(s: string, k: int)
  requires 0 <= k <= |s| / 2
  ensures (forall i :: 0 <= i < k ==> s[i] == s[|s| - 1 - i]) <==> 
          (forall i :: 0 <= i < k && i <= |s| - 1 - i ==> s[i] == s[|s| - 1 - i])
{
}
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)

  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Using lemma to strengthen loop invariant for verification */
{
  if |s| == 0 {
    result := true;
  } else {
    result := true;
    var i := 0;
    while i < |s| / 2
      invariant 0 <= i <= |s| / 2
      invariant forall j :: 0 <= j < i ==> s[j] == s[|s| - 1 - j]
    {
      palindrome_helper(s, i + 1);
      if s[i] != s[|s| - 1 - i] {
        result := false;
        return;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
