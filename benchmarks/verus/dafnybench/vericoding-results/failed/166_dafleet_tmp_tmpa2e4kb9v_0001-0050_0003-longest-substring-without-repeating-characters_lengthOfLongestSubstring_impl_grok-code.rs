use vstd::prelude::*;

verus! {

/* https://leetcode.com/problems/longest-substring-without-repeating-characters/
Given a string s, find the length of the longest substring without repeating characters.

Example 1:
Input: s = "abcabcbb"
Output: 3
Explanation: The answer is "abc", with the length of 3.
*/


// a left-inclusive right-exclusive interval:
pub struct Interval {
    pub start: int,
    pub end: int,
}

impl Interval {
    pub open spec fn valid(self) -> bool {
        self.start <= self.end
    }
}

pub open spec fn length(iv: Interval) -> int {
    iv.end - iv.start
}

pub open spec fn valid_interval(s: Seq<char>, iv: Interval) -> bool {
    &&& 0 <= iv.start <= iv.end <= s.len()                             // interval is in valid range
    &&& forall|i: int, j: int| iv.start <= i < j < iv.end ==> s[i] != s[j]   // no repeating characters in interval
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
// Empty, as no changes needed
// </vc-helpers>

// <vc-spec>
fn lengthOfLongestSubstring(s: Seq<char>) -> (result: (usize, Ghost<Interval>))
    ensures 
        valid_interval(s, result.1@) && length(result.1@) == result.0 as int,    /** `result.1@` is valid */
        forall|iv: Interval| valid_interval(s, iv) ==> length(iv) <= result.0 as int,  /** `result.1@` is longest */
// </vc-spec>
// <vc-code>
{
    let mut lo: int = 0;
    let mut hi: int = 0;
    let mut best_len: int = 0;
    let mut best_iv: Interval = Interval { start: 0, end: 0 };
    let mut map: Map<char, int> = Map::empty();
    
    assert(valid_interval(s, best_iv));
    
    assert(forall |iv: Interval| 
        valid_interval(s, iv) && iv.end <= hi ==> length(iv) <= best_len);
    
    while hi < s.len()
        invariant
            0 <= lo <= hi <= s.len()
            &&& (forall |c| #[trigger] map.contains_key(c) ==> lo <= map[c] < hi)
            &&& (forall |i: int, j: int| lo <= i < j < hi ==> s[i] != s[j])
            &&& valid_interval(s, best_iv)
            &&& best_len == length(best_iv)
            &&& (forall |iv: Interval| valid_interval(s, iv) && iv.end <= hi ==> length(iv) <= best_len)
    {
        let chi = s[hi];
        if map.contains_key(chi) {
            let last = map[chi];
            assert(last >= lo && last < hi);
            map = map.insert(chi, hi);
            lo = lo.max(last + 1);
        } else {
            map = map.insert(chi, hi);
        }
        // After updating lo, assert the window lo..hi+1 is valid
        assert(forall |i: int, j: int| lo <= i < j <= hi ==> s[i] != s[j]);
        let current_iv_end = hi + 1;
        let current_iv = Interval { start: lo, end: current_iv_end };
        assert(valid_interval(s, current_iv));
        let curr_len = current_iv_end - lo;
        if curr_len > best_len {
            best_len = curr_len;
            best_iv = current_iv;
        }
        proof {
            // Preserve invariants after potential update
            assert(valid_interval(s, best_iv));
            assert(best_len == length(best_iv));
            // Assert that the new best_len is the max length for intervals ending <= hi
            if curr_len > old(best_len) {
                // Updated, so best_len now equals the length of the current valid interval (longest ending at hi + 1)
            }
            assert(forall |iv: Interval| valid_interval(s, iv) && iv.end <= hi && iv.end != old(hi) ==> length(iv) <= old(best_len));
            assert(length(current_iv) == curr_len);
            if curr_len <= best_len {
                assert(best_len == old(best_len));
            }
        }
        hi = hi + 1;
    }
    
    proof {
        // Ensure postconditions hold
        assert(valid_interval(s, best_iv));
        assert(best_len == length(best_iv));
        // The invariant ensures the forall since hi == s.len()
        assert(forall|iv: Interval| valid_interval(s, iv) && iv.end <= s.len() ==> length(iv) <= best_len);
        assert(forall|iv: Interval| valid_interval(s, iv) ==> iv.end <= s.len());
    }
    
    return (best_len as usize, Ghost(best_iv));
}
// </vc-code>

fn main() {}

}