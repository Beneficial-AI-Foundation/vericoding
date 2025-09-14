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
ghost predicate validWindow(s: string, lo: int, hi: int, chars: set<char>) {
  && 0 <= lo <= hi <= |s|
  && chars == set i | lo <= i < hi :: s[i]
  && |chars| == hi - lo
}

lemma validWindowImpliesValidInterval(s: string, lo: int, hi: int, chars: set<char>)
  requires validWindow(s, lo, hi, chars)
  ensures valid_interval(s, (lo, hi))
{
  var iv := (lo, hi);
  assert 0 <= iv.0 <= iv.1 <= |s|;
  
  forall i, j | iv.0 <= i < j < iv.1
    ensures s[i] != s[j]
  {
    assert s[i] in chars && s[j] in chars;
    if s[i] == s[j] {
      assert |chars| < hi - lo;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    return 0, (0, 0);
  }
  
  var lo := 0;
  var hi := 0;
  var chars: set<char> := {};
  var best_len := 0;
  ghost var best_interval := (0, 0);
  
  while hi < |s|
    invariant 0 <= lo <= hi <= |s|
    invariant validWindow(s, lo, hi, chars)
    invariant valid_interval(s, best_interval)
    invariant length(best_interval) == best_len
    invariant forall iv | valid_interval(s, iv) && iv.1 <= hi :: length(iv) <= best_len
  {
    if s[hi] in chars {
      chars := chars - {s[lo]};
      lo := lo + 1;
    } else {
      chars := chars + {s[hi]};
      hi := hi + 1;
      
      if hi - lo > best_len {
        best_len := hi - lo;
        best_interval := (lo, hi);
        validWindowImpliesValidInterval(s, lo, hi, chars);
      }
    }
  }
  
  n := best_len;
  best_iv := best_interval;
}
// </vc-code>

