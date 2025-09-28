// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count(hi: nat, s: Seq<int>) -> int
    recommends 0 <= hi <= s.len()
    decreases hi
{
    if hi == 0 {
        0
    } else if s[hi-1] % 2 == 0 {
        1 + count((hi-1) as nat, s)
    } else {
        count((hi-1) as nat, s)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_count(count_index: usize, a: Seq<int>, b: &mut Vec<int>) -> (p: usize)
    requires count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len())
    ensures p == count(count_index as nat, a)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected logic to use sequence 'a' and fixed type errors */
    let mut i: usize = 0;
    let mut p: usize = 0;
    while i < count_index
        invariant
            0 <= i <= count_index,
            p == count(i as nat, a),
        decreases count_index - i
    {
        if a.index(i as int) % (2 as int) == (0 as int) {
            p = p + 1;
        }
        i = i + 1;
    }
    p
}
// </vc-code>

}
fn main() {}