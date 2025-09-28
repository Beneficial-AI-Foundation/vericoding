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
proof fn lemma_valid_interval_empty(s: Seq<char>, start: int)
    requires 0 <= start <= s.len()
    ensures valid_interval(s, Interval { start: start, end: start })
{
}

proof fn lemma_valid_interval_monotonic(s: Seq<char>, iv1: Interval, iv2: Interval)
    requires 
        valid_interval(s, iv1),
        iv2.start >= iv1.start,
        iv2.end <= iv1.end,
        iv1.start <= iv2.start <= iv2.end <= iv1.end
    ensures valid_interval(s, iv2)
{
}

proof fn lemma_sliding_window_property(s: Seq<char>, lo: int, hi: int, c: char)
    requires 
        0 <= lo < hi <= s.len(),
        s[hi - 1] == c,
        forall|i: int, j: int| lo <= i < j < hi ==> s[i] != s[j]
    ensures
        forall|start: int| lo <= start < hi - 1 ==> !valid_interval(s, Interval { start: start, end: hi })
{
}

spec fn contains_char(s: Seq<char>, start: int, end: int, c: char) -> bool {
    exists|i: int| start <= i < end && s[i] == c
}

proof fn lemma_extend_valid_interval(s: Seq<char>, iv: Interval, new_end: int)
    requires 
        valid_interval(s, iv),
        iv.end < new_end <= s.len(),
        !contains_char(s, iv.start, iv.end, s[new_end - 1])
    ensures valid_interval(s, Interval { start: iv.start, end: new_end })
{
}

proof fn lemma_no_repeat_in_window(s: Seq<char>, lo: int, hi: int)
    requires 
        0 <= lo <= hi <= s.len(),
        forall|i: int| lo <= i < hi ==> s[i] != s[hi]
    ensures 
        forall|i: int, j: int| lo <= i < j <= hi ==> s[i] != s[j]
{
}

proof fn lemma_best_remains_valid(s: Seq<char>, iv: Interval, new_hi: int)
    requires 
        valid_interval(s, iv),
        iv.end <= new_hi <= s.len()
    ensures 
        forall|test_iv: Interval| valid_interval(s, test_iv) && test_iv.end <= new_hi ==> length(test_iv) <= length(iv) || valid_interval(s, iv)
{
}

proof fn lemma_current_window_valid(s: Seq<char>, lo: int, hi: int)
    requires 
        0 <= lo <= hi < s.len(),
        forall|i: int| lo <= i < hi ==> s[i] != s[hi]
    ensures 
        forall|i: int, j: int| lo <= i < j <= hi ==> s[i] != s[j]
{
    assert(forall|i: int, j: int| lo <= i < j < hi ==> s[i] != s[j]);
    assert(forall|i: int| lo <= i < hi ==> s[i] != s[hi]);
}

proof fn lemma_window_no_duplicates(s: Seq<char>, lo: int, hi: int, pos: int)
    requires 
        lo <= pos < hi,
        forall|i: int| lo <= i < pos ==> s[i] != s[hi],
        s[pos] == s[hi]
    ensures 
        forall|i: int, j: int| (pos + 1) <= i < j <= hi ==> s[i] != s[j]
{
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
    if s.len() == 0 {
        return (0, Ghost(Interval { start: 0, end: 0 }));
    }

    let mut lo: usize = 0;
    let mut hi: usize = 0;
    let mut best_len: usize = 0;
    let mut best_iv: Ghost<Interval> = Ghost(Interval { start: 0, end: 0 });
    
    proof {
        lemma_valid_interval_empty(s, 0);
    }
    
    while hi < s.len()
        invariant
            lo <= hi <= s.len(),
            valid_interval(s, best_iv@),
            best_len == length(best_iv@) as usize,
            forall|iv: Interval| valid_interval(s, iv) && iv.end <= hi ==> length(iv) <= best_len as int,
            forall|i: int, j: int| lo <= i < j < hi ==> s[i] != s[j],
    {
        let mut pos: usize = lo;
        let target_char = s[hi as int];
        
        while pos < hi
            invariant
                lo <= pos <= hi,
                forall|i: int| lo <= i < pos ==> s[i] != target_char,
        {
            if s[pos as int] == target_char {
                break;
            }
            pos += 1;
        }
        
        if pos < hi {
            lo = pos + 1;
            proof {
                lemma_window_no_duplicates(s, (pos + 1) as int, hi as int, pos as int);
            }
        }
        
        let current_len = hi + 1 - lo;
        let current_iv = Interval { start: lo as int, end: (hi + 1) as int };
        
        proof {
            if pos < hi {
                assert(s[pos as int] == target_char);
                assert(forall|i: int, j: int| (pos + 1) <= i < j <= hi ==> s[i] != s[j]);
                assert(forall|i: int| (pos + 1) <= i < hi ==> s[i] != s[hi as int]);
            } else {
                assert(forall|i: int| lo <= i < hi ==> s[i] != target_char);
                assert(forall|i: int| lo <= i < hi ==> s[i] != s[hi as int]);
            }
            
            assert(forall|i: int, j: int| lo <= i < j < (hi + 1) ==> s[i] != s[j]);
        }
        
        assert(valid_interval(s, current_iv));
        
        if current_len > best_len {
            best_len = current_len;
            best_iv = Ghost(current_iv);
        }
        
        hi += 1;
    }
    
    (best_len, best_iv)
}
// </vc-code>

fn main() {}

}