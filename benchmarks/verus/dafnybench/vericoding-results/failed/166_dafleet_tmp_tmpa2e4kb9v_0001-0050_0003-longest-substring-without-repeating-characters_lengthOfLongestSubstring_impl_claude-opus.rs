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
// Helper to check if a character exists in the current window
pub open spec fn char_in_window(s: Seq<char>, c: char, lo: int, hi: int) -> bool
    recommends lo <= hi, hi <= s.len()
{
    exists|i: int| lo <= i < hi && #[trigger] s[i] == c
}

// Helper lemma: extending a valid interval by one character
proof fn extend_valid_interval(s: Seq<char>, lo: int, hi: int)
    requires
        0 <= lo <= hi < s.len(),
        valid_interval(s, Interval { start: lo, end: hi }),
        !char_in_window(s, s[hi], lo, hi),
    ensures
        valid_interval(s, Interval { start: lo, end: hi + 1 }),
{
    let iv = Interval { start: lo, end: hi + 1 };
    assert forall|i: int, j: int| iv.start <= i < j < iv.end implies s[i] != s[j] by {
        if j == hi {
            // s[j] is the new character
            assert(!char_in_window(s, s[hi], lo, hi));
            assert(i >= lo && i < hi);
            assert(s[i] != s[j]);
        } else {
            // Both i and j are in the old interval
            assert(valid_interval(s, Interval { start: lo, end: hi }));
        }
    }
}

// Helper lemma: shrinking from the left preserves no-repeat property
proof fn shrink_valid_interval(s: Seq<char>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        valid_interval(s, Interval { start: lo, end: hi }),
    ensures
        valid_interval(s, Interval { start: lo + 1, end: hi }),
{
    let iv = Interval { start: lo + 1, end: hi };
    assert forall|i: int, j: int| iv.start <= i < j < iv.end implies s[i] != s[j] by {
        assert(valid_interval(s, Interval { start: lo, end: hi }));
        assert(lo <= i < j < hi);
    }
}

// Helper lemma: for maintaining invariant (B)
proof fn maintain_monotonicity(s: Seq<char>, lo: int, hi: int, new_lo: int)
    requires
        0 <= lo <= new_lo <= hi < s.len(),
        forall|iv: Interval|
            valid_interval(s, iv) && iv.end > hi ==>
            iv.start >= lo,
    ensures
        forall|iv: Interval|
            valid_interval(s, iv) && iv.end > hi ==>
            iv.start >= new_lo,
{
    assert forall|iv: Interval| valid_interval(s, iv) && iv.end > hi implies iv.start >= new_lo by {
        if valid_interval(s, iv) && iv.end > hi {
            assert(iv.start >= lo);
            assert(iv.start >= new_lo);
        }
    }
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
    let mut lo: usize = 0;
    let mut hi: usize = 0;
    let mut best_iv: Ghost<Interval> = Ghost(Interval { start: 0, end: 0 });
    let mut best_len: usize = 0;
    
    // Initial interval [0, 0) is valid
    assert(valid_interval(s, Interval { start: 0, end: 0 }));
    assert(valid_interval(s, best_iv@));
    
    while hi < s.len()
        invariant
            0 <= lo <= hi <= s.len(),
            valid_interval(s, Interval { start: lo as int, end: hi as int }),
            valid_interval(s, best_iv@),
            length(best_iv@) == best_len as int,
            // (A) best_iv is the longest valid interval in s[..hi]
            forall|iv: Interval| 
                valid_interval(s, iv) && iv.end <= hi as int ==> 
                length(iv) <= best_len as int,
            // (B) Monotonicity: no valid interval ending after hi can start before lo
            forall|iv: Interval|
                valid_interval(s, iv) && iv.end > hi as int ==>
                iv.start >= lo as int,
    {
        let c = s[hi as int];
        
        // Check if character is already in window
        let mut found = false;
        let mut j: usize = lo;
        while j < hi
            invariant
                lo <= j <= hi,
                found == char_in_window(s, c, lo as int, j as int),
        {
            if s[j as int] == c {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if found {
            // Shrink window from left until we remove the duplicate
            while lo < hi && s[lo as int] != c
                invariant
                    0 <= lo <= hi < s.len(),
                    valid_interval(s, Interval { start: lo as int, end: hi as int }),
                    char_in_window(s, c, lo as int, hi as int),
                    // Maintain monotonicity during shrinking
                    forall|iv: Interval|
                        valid_interval(s, iv) && iv.end > hi as int ==>
                        iv.start >= lo as int,
            {
                proof {
                    shrink_valid_interval(s, lo as int, hi as int);
                    maintain_monotonicity(s, lo as int, hi as int, (lo + 1) as int);
                }
                lo = lo + 1;
            }
            // Now s[lo] == c, remove it
            proof {
                shrink_valid_interval(s, lo as int, hi as int);
                maintain_monotonicity(s, lo as int, hi as int, (lo + 1) as int);
            }
            lo = lo + 1;
        }
        
        // Now we can safely add c to the window
        proof {
            assert(!char_in_window(s, c, lo as int, hi as int));
            extend_valid_interval(s, lo as int, hi as int);
        }
        hi = hi + 1;
        
        // Update best if current window is longer
        let current_len = hi - lo;
        if current_len > best_len {
            best_len = current_len;
            best_iv = Ghost(Interval { start: lo as int, end: hi as int });
        }
        
        // Prove invariant (A) is maintained
        assert forall|iv: Interval| 
            valid_interval(s, iv) && iv.end <= hi as int implies
            length(iv) <= best_len as int by 
        {
            if valid_interval(s, iv) && iv.end <= hi as int {
                if iv.end < hi as int {
                    // Was already considered in previous iterations
                    assert(iv.end <= (hi - 1) as int);
                } else {
                    // iv.end == hi
                    if iv.start < lo as int {
                        // By invariant (B) from previous iteration, this is impossible
                        assert(false);
                    } else {
                        // iv.start >= lo, so length(iv) <= hi - lo = current_len <= best_len
                        assert(length(iv) == iv.end - iv.start);
                        assert(length(iv) <= hi as int - lo as int);
                        assert(length(iv) <= current_len as int);
                        assert(length(iv) <= best_len as int);
                    }
                }
            }
        }
        
        // Prove invariant (B) is maintained
        assert forall|iv: Interval|
            valid_interval(s, iv) && iv.end > hi as int implies
            iv.start >= lo as int by
        {
            if valid_interval(s, iv) && iv.end > hi as int {
                // If iv includes position hi, it cannot include any position < lo
                // because we just ensured s[hi] doesn't repeat in [lo, hi)
                if iv.start < lo as int && hi as int < iv.end {
                    // iv contains position hi
                    assert(iv.start <= hi as int && hi as int < iv.end);
                    // s[hi] appears at position hi within iv
                    
                    // Check if s[hi] appears elsewhere in iv
                    let mut k: int = iv.start;
                    while k < hi as int
                        invariant iv.start <= k <= hi as int
                    {
                        if k >= lo as int {
                            // We know s[hi] doesn't appear in [lo, hi)
                            assert(s[k] != s[hi as int]);
                        } else {
                            // k < lo, and we removed all occurrences of s[hi] before lo
                            if s[k] == s[hi as int] {
                                // This would violate the no-repeat property of iv
                                assert(valid_interval(s, iv));
                                assert(k < hi as int);
                                assert(s[k] != s[hi as int]); // Contradiction
                            }
                        }
                        k = k + 1;
                    }
                    assert(false); // Can't happen
                }
                assert(iv.start >= lo as int);
            }
        }
    }
    
    // Prove postcondition
    assert forall|iv: Interval| valid_interval(s, iv) implies length(iv) <= best_len as int by {
        if valid_interval(s, iv) {
            assert(iv.end <= s.len());
            assert(iv.end <= hi as int);
        }
    }
    
    (best_len, best_iv)
}
// </vc-code>

fn main() {}

}