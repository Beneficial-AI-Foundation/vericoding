/* https://leetcode.com/problems/longest-substring-without-repeating-characters/
Given a string s, find the length of the longest substring without repeating characters.

Example 1:
Input: s = "abcabcbb"
Output: 3
Explanation: The answer is "abc", with the length of 3.
*/


// a left-inclusive right-exclusive interval:
type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)                             // interval is in valid range
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])   // no repeating characters in interval
}

// Below shows an efficient solution using standard "sliding window" technique. 
// For verification simplicity, we pretend as if:
// - `set` were Python set (or even better, a fixed-size array -- if the "alphabet" is small)
//
// `best_iv` is for verification purpose, not returned by the real program, thus `ghost`.

/* Discussions
1. The "sliding window" technique is the most "fancy" part of the solution,
  ensuring an O(n) time despite the O(n^2) search space.
  The reason why it works lies in the last two invariants: (A) and (B).

  Invariant (A) is simply a "partial" guarantee for the longest valid substring in `s[..hi]`,
  so once the loop finishes, as `hi == |s|`, this "partial" guarantee becomes "full".

  Invariant (B) is crucial: it encodes why we can monotonically increase `lo` as we increase `hi`.
  What's the "intuition" behind that? Let me share an "informal proof" below:

    Let `sub(i)` be the longest valid substring whose last character is `s[i]`.
    Apparently, the final answer will be "the longest among the longests", i.e.
    `max(|sub(0)|, |sub(1)|, ..., |sub(|s|-1)|)`.

    Now, notice that the "starting position" of `sub(i)` is monotonically increasing regarding `i`!
    Otherwise, imagine `sub(i+1)` started at `j` while `sub(i)` started at `j+1` (or even worse),
    then `sub(i)` could be made longer (by starting at `j` instead).
    This is an obvious contradiction.

    Therefore, when we search for the starting position of `sub(i)` (the `lo`) for each `i` (the `hi`),
    there's no need to "look back".

2. The solution above can be made more efficient, using "jumping window" instead of "sliding window".
  Namely, we use a dict (instead of set) to look up the "position of repetition",
  and move `lo` right after that position at once.

  You can even "early terminate" (based on `lo`) when all remaining intervals are doomed "no longer",
  resulting in even fewer number of loop iterations.
  (Time complexity will still be O(n), though.)

  The corresponding verification code is shown below:
*/


// For verification simplicity, we pretend as if:
// - `map` were Python dict (or even better, a fixed-size array -- if the "alphabet" is small)

// Bonus Question:
//   "Why can we safely use (C) instead of (D) as the loop condition? Won't `hi` go out-of-bound?"
// Can you figure it out?

// <vc-helpers>
ghost predicate valid_prefix(s: string, len: int) {
  && 0 <= len <= |s|
  && forall i,j :: 0 <= i < j < len ==> s[i] != s[j]
}

ghost predicate set_represents_window(s: string, lo: int, hi: int, currentSet: set<char>) {
  currentSet == (set i | lo <= i < hi :: s[i])
}
// </vc-helpers>

// <vc-spec>
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
// </vc-spec>
// <vc-code>
{
  var res := 0;
  ghost var best_iv := (0,0);
  if |s| == 0 {
    n := 0;
    return n, best_iv;
  }
  var lo := 0;
  var hi := 0;
  var currentSet: set<char> := {};
  while hi < |s| 
    invariant 0 <= lo <= hi <= |s|
    invariant |currentSet| <= hi - lo
    invariant set_represents_window(s, lo, hi, currentSet)
    invariantforall i,j | lo <= i < j < hi :: s[i] != s[j]  // no repeats in window
    invariant valid_prefix(s, hi)
    decreases |s| - hi
  {
    if s[hi] in currentSet {
      while lo < hi && s[hi] in currentSet 
        invariant lo <= hi
        invariant s[hi] in currentSet
        invariant set_represents_window(s, lo, hi, currentSet)
        invariant forall k,l | lo <= k < l < hi :: s[k] != s[l]  // no repeats in current window
      {
        currentSet := currentSet - {s[lo]};
        lo := lo + 1;
      }
    }
    assert set_represents_window(s, lo, hi, currentSet);
    if hi - lo + 1 > res {
      res := hi - lo + 1;
      best_iv := (lo, hi + 1);
    }
    currentSet := currentSet + {s[hi]};
    assert s[hi] !in currentSet;
    hi := hi + 1;
  }
  n := res;
  return n, best_iv;
}
// </vc-code>

