// <vc-helpers>
type interval = (int, int)

lemma valid_interval_subset(s: string, iv1: interval, iv2: interval)
  requires valid_interval(s, iv1)
  requires 0 <= iv2.0 <= iv2.1 <= |s|
  requires iv1.0 <= iv2.0 && iv2.1 <= iv1.1
  ensures valid_interval(s, iv2)
{
}

lemma extending_valid_interval(s: string, lo: int, hi: int)
  requires 0 <= lo <= hi < |s|
  requires forall i, j | lo <= i < j < hi :: s[i] != s[j]
  requires s[hi] !in (set i | lo <= i < hi :: s[i])
  ensures forall i, j | lo <= i < j < hi + 1 :: s[i] != s[j]
{
}
// </vc-helpers>

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

// <vc-spec>
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    n := 0;
    best_iv := (0, 0);
    return;
  }
  
  var lo := 0;
  var hi := 0;
  var window := {};
  n := 0;
  best_iv := (0, 0);
  
  while hi < |s|
    invariant 0 <= lo <= hi <= |s|
    invariant window == set i | lo <= i < hi :: s[i]
    invariant forall i, j | lo <= i < j < hi :: s[i] != s[j]  // current window is valid
    invariant valid_interval(s, best_iv) && length(best_iv) == n
    invariant forall iv | valid_interval(s, iv) && iv.1 <= hi :: length(iv) <= n
  {
    if s[hi] in window {
      // Remove characters from left until s[hi] is no longer in window
      while s[hi] in window
        invariant lo <= hi
        invariant window == set i | lo <= i < hi :: s[i]
        invariant forall i, j | lo <= i < j < hi :: s[i] != s[j]
        decreases hi - lo
      {
        window := window - {s[lo]};
        lo := lo + 1;
      }
    }
    
    // Add s[hi] to window
    extending_valid_interval(s, lo, hi);
    window := window + {s[hi]};
    
    // Update best if current window is better (before incrementing hi)
    if hi + 1 - lo > n {
      n := hi + 1 - lo;
      best_iv := (lo, hi + 1);
    }
    
    hi := hi + 1;
  }
}
// </vc-code>

/* Discussions
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