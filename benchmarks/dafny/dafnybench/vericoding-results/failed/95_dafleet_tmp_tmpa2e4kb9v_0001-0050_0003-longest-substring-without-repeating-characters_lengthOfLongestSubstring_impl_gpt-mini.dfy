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
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
// </vc-spec>
// <vc-code>
{
  ghost var gbest_iv: interval := (0, 0);
  var gbest_len: int := 0;
  var lo := 0;
  var hi := 0;
  var last: map<char, int> := map[];

  while hi < |s|
    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant valid_interval(s, gbest_iv)
    invariant gbest_len == length(gbest_iv)
    invariant 0 <= gbest_len <= |s|
    invariant forall iv | valid_interval(s, iv) && iv.1 <= hi :: length(iv) <= gbest_len
    invariant forall c :: c in last ==> 0 <= last[c] < hi
    invariant forall i :: lo <= i < hi ==> last[s[i]] == i
  {
    var c := s[hi];

    // snapshot previous state to help the verifier
    ghost var prevLast := last;
    ghost var prev_lo := lo;
    ghost var old_hi := hi;
    ghost var prev_hi := hi;

    // previous mapping property (from loop invariant)
    assert forall i :: prev_lo <= i < prev_hi ==> prevLast[s[i]] == i;

    if c in prevLast && prevLast[c] >= prev_lo {
      lo := prevLast[c] + 1;
    }
    // lo never decreases
    assert lo >= prev_lo;
    // if c occurred before, its previous position is strictly before lo now
    if c in prevLast {
      assert prevLast[c] < lo;
    }

    hi := hi + 1;
    last := last[c := old_hi];

    // For indices strictly before old_hi, entries in `last` still map to their indices.
    // For i in [lo, old_hi), since prevLast[s[i]] == i and prevLast[c] < lo, we know s[i] != c,
    // hence last[s[i]] == prevLast[s[i]] == i.
    assert forall i :: lo <= i < old_hi ==> last[s[i]] == i;
    // For the new position old_hi, we assigned last[s[old_hi]] == old_hi
    assert last[s[old_hi]] == old_hi;
    // Combine to cover the whole new window [lo, hi)
    assert forall i :: lo <= i < hi ==> last[s[i]] == i;

    // All entries in `last` are within [0, hi)
    // For chars other than c, prevLast[*] < prev_hi == old_hi < hi
    // For c, last[c] == old_hi < hi
    assert forall ch :: ch in last ==> 0 <= last[ch] < hi;

    // Re-establish that the new window (lo, hi) has no duplicates.
    //  - if j < old_hi, it follows from the previous valid_interval (subset)
    //  - if j == old_hi, we know no i in [lo, old_hi) has s[i] == c
    assert forall i, j | lo <= i < j < old_hi :: s[i] != s[j];
    assert forall i :: lo <= i < old_hi ==> s[i] != c;
    assert forall i, j | lo <= i < j < hi :: s[i] != s[j];

    if hi - lo > gbest_len {
      gbest_len := hi - lo;
      gbest_iv := (lo, hi);
    }
  }

  n := gbest_len;
  best_iv := gbest_iv;
}
// </vc-code>

