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
spec fn is_contained_in(i: int, j: int, s: Seq<char>) -> bool {
    0 <= i && i <= j && j <= s.len()
}

spec fn distinct_subseq(s: Seq<char>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> s[i] != s[j]
}

proof fn lemma_distinct_monotonic(s: Seq<char>, start: int, mid: int, end: int)
    requires
        is_contained_in(start, end, s),
        distinct_subseq(s, start, end),
        start <= mid <= end,
    ensures
        distinct_subseq(s, start, mid) && distinct_subseq(s, mid, end),
{
}

proof fn lemma_extend_distinct(s: Seq<char>, start: int, end: int, hi: int)
    requires
        is_contained_in(start, end, s),
        distinct_subseq(s, start, end),
        end < hi,
        hi <= s.len(),
        forall|i: int| start <= i < end ==> s[i] != s[hi],
    ensures
        distinct_subseq(s, start, hi),
{
}

proof fn lemma_shrink_distinct(s: Seq<char>, start: int, end: int, new_start: int)
    requires
        is_contained_in(start, end, s),
        start <= new_start <= end,
        distinct_subseq(s, start, end),
    ensures
        distinct_subseq(s, new_start, end),
{
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn find_char(s: Seq<char>, start: int, end: int, c: char) -> int {
    choose|i: int| start <= i < end && s[i] == c
}

spec fn has_char(s: Seq<char>, start: int, end: int, c: char) -> bool {
    exists|i: int| start <= i < end && s[i] == c
}

spec fn valid_interval(s: Seq<char>, iv: Interval) -> bool {
    &&& 0 <= iv.start <= iv.end <= s.len()
    &&& distinct_subseq(s, iv.start, iv.end)
}

spec fn length(iv: Interval) -> int {
    iv.end - iv.start
}

proof fn lemma_seen_dup_maintains_invariant(s: Seq<char>, lo: int, hi: int, dup_index: int)
    requires
        is_contained_in(lo, hi, s),
        distinct_subseq(s, lo, hi),
        lo <= dup_index < hi,
        s[dup_index] == s[hi],
    ensures
        distinct_subseq(s, dup_index + 1, hi),
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
    let mut lo: usize = 0;
    let mut hi: usize = 0;
    let mut max_len: usize = 0;
    let mut ghost_max_iv = Interval { start: 0, end: 0 };
    
    while hi < s.len()
        invariant
            0 <= lo <= hi <= s.len(),
            max_len <= s.len(),
            valid_interval(s, ghost_max_iv),
            length(ghost_max_iv) == max_len as int,
            forall|iv: Interval| valid_interval(s, iv) && iv.end <= hi as int ==> length(iv) <= max_len as int,
            distinct_subseq(s, lo as int, hi as int),
    {
        let mut seen_dup = false;
        let mut dup_index: usize = lo;
        
        while dup_index < hi
            invariant
                lo <= dup_index <= hi,
                distinct_subseq(s, lo as int, dup_index as int),
                seen_dup ==> (lo <= dup_index - 1 < hi && s[dup_index - 1] == s[hi]),
        {
            if s[dup_index] == s[hi] {
                seen_dup = true;
                break;
            }
            dup_index += 1;
        }
        
        if seen_dup {
            proof {
                lemma_seen_dup_maintains_invariant(s, lo as int, hi as int, dup_index as int);
            }
            lo = dup_index + 1;
        }
        
        proof {
            lemma_extend_distinct(s, lo as int, hi as int, hi as int + 1);
        }
        hi += 1;
        
        let current_len = hi - lo;
        if current_len > max_len {
            max_len = current_len;
            ghost_max_iv = Interval { start: lo as int, end: hi as int };
        }
    }
    
    (max_len, Ghost(ghost_max_iv))
}
// </vc-code>

fn main() {}

}