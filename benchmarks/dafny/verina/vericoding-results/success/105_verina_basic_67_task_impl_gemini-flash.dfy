// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the invariant and fixed the `ensures` clause to reflect the definition of a palindrome correctly. */
predicate IsPalindromeHelper(x: seq<char>, lo: int, hi: int)
  requires 0 <= lo <= hi + 1 <= |x|
  decreases hi - lo
  // Fixed the `ensures` clause to reflect the definition of a palindrome correctly.
  ensures IsPalindromeHelper(x, lo, hi) <==> (forall i :: lo <= i <= hi ==> x[i] == x[hi - (i - lo)])
{
  if lo >= hi then
    true
  else
    x[lo] == x[hi] && IsPalindromeHelper(x, lo + 1, hi - 1)
}
// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): wrapped the `if` statement in a block and maintained the logic for calling the helper. */
{
  if |x| == 0 {
    result := true;
  } else {
    result := IsPalindromeHelper(x, 0, |x| - 1);
  }
}
// </vc-code>
