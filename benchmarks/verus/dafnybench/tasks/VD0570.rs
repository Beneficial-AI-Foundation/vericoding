// <vc-preamble>
use vstd::prelude::*;

verus! {

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
    &&& 0 <= iv.start <= iv.end <= s.len()
    &&& forall|i: int, j: int| iv.start <= i < j < iv.end ==> s[i] != s[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lengthOfLongestSubstring(s: Seq<char>) -> (result: (usize, Ghost<Interval>))
    ensures 
        (valid_interval(s, result.1@) && length(result.1@) == result.0 as int),
        (forall|iv: Interval| valid_interval(s, iv) ==> length(iv) <= result.0 as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}