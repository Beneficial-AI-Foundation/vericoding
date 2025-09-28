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
use vstd::prelude::*;
use vstd::set::*;
use vstd::map::*;

pub open spec fn length(iv: Interval) -> int {
    iv.end - iv.start
}

pub open spec fn is_distinct_chars(s: Seq<char>) -> bool {
    forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

pub open spec fn valid_interval(s: Seq<char>, iv: Interval) -> bool {
    &&& 0 <= iv.start <= iv.end <= s.len()
    &&& is_distinct_chars(s.subsequence(iv.start, iv.end))
}
// </vc-helpers>

// <vc-spec>
fn lengthOfLongestSubstring(s: Seq<char>) -> (result: (usize, Ghost<Interval>))
    ensures 
        valid_interval(s, result.1@) && length(result.1@) == result.0 as int,    /** `result.1@` is valid */
        forall|iv: Interval| valid_interval(s, iv) ==> length(iv) <= result.0 as int,  /** `result.1@` is longest */
// </vc-spec>
// <vc-code>
{
    let s_len = s.len() as int;

    if s_len == 0 {
        return (0, Ghost(Interval { start: 0, end: 0 }));
    }

    let mut char_last_idx: Map<char, int> = Map::empty();

    let mut lo: int = 0;
    let mut hi: int = 0;
    let mut max_len: int = 0;
    let mut best_iv: Ghost<Interval> = Ghost(Interval { start: 0, end: 0 });

    while hi < s_len
        invariant auto
            0 <= lo <= hi <= s_len,

            valid_interval(s, best_iv@),
            max_len == length(best_iv@),
            forall |iv: Interval| 0 <= iv.start <= iv.end <= hi && valid_interval(s, iv) ==> length(iv) <= max_len,

            // The substring `s[lo..hi]` does not contain any repeating characters.
            is_distinct_chars(s.subsequence(lo, hi)),
            
            // For any char c in char_last_idx, its value idx is its last observed index
            // in s[0..hi-1].
            forall |c: char| char_last_idx.contains_key(c) ==> {
                let idx = char_last_idx.get(c).unwrap();
                &&& 0 <= idx < hi
                &&& s[idx] == c
                &&& (forall |k: int| idx < k < hi ==> s[k] != c)
            },
           
        decreases s_len - hi
    {
        let current_char = s[hi];
        
        let old_lo = lo;
        let old_char_last_idx = char_last_idx;

        if char_last_idx.contains_key(current_char) {
            let last_idx_of_current_char = char_last_idx.get(current_char).unwrap();
            
            if last_idx_of_current_char >= lo {
                lo = last_idx_of_current_char + 1;
            }
        }
        
        proof {
            assert(0 <= hi < s_len);
        }
        char_last_idx = char_last_idx.insert(current_char, hi);

        let current_len = hi - lo + 1;
        if current_len > max_len {
            max_len = current_len;
            best_iv = Ghost(Interval { start: lo, end: hi + 1 });
        }
        
        proof {
            // Prove `is_distinct_chars(s.subsequence(lo, hi+1))`
            let c = s[hi];
            let s_sub_lo_hi_old = s.subsequence(old_lo, hi);
            assert(is_distinct_chars(s_sub_lo_hi_old)); // from invariant

            if old_char_last_idx.contains_key(c) {
                let last_idx = old_char_last_idx.get(c).unwrap();
                if last_idx >= old_lo {
                    // lo moved to last_idx + 1
                    assert(lo == last_idx + 1);
                    assert(s[last_idx] == c); // from char_last_idx invariant
                    assert(forall |k: int| last_idx < k < hi ==> s[k] != c); // from char_last_idx invariant
                    assert(is_distinct_chars(s.subsequence(lo, hi)));
                    assert(forall |k: int| lo <= k < hi ==> s[k] != c);
                } else {
                    // lo did not move, current_char not in s[old_lo..hi]
                    assert(lo == old_lo);
                    assert(forall |k: int| old_lo <= k < hi ==> s[k] != c);
                    assert(is_distinct_chars(s.subsequence(lo, hi)));
                }
            } else {
                // current_char not seen before hi. So it's not in s[old_lo..hi].
                assert(lo == old_lo);
                assert(forall |k: int| old_lo <= k < hi ==> s[k] != c);
                assert(is_distinct_chars(s.subsequence(lo, hi)));
            }
            // In all cases, after updating `lo`, `is_distinct_chars(s.subsequence(lo, hi))` holds.
            // And s[hi] is the new character added at the end.
            // When we advance `hi` to `hi+1`, we need to show `is_distinct_chars(s.subsequence(lo, hi+1))`.
            // Because `s[lo..hi]` is distinct and `s[hi]` is not in `s[lo..hi]`, then `s[lo..hi+1]` is distinct.
        }

        hi = hi + 1;
    }
    
    (max_len as usize, best_iv)
}
// </vc-code>

fn main() {}

}